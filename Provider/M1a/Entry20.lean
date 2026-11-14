import M1a.Tail20
import GetEntry.Full
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 800000
namespace ArmCert.Eval.M1a
open S1OuterSetup S1EntryWP

/-- The actual S1Walk result at a normal EL2&0 level-3 leaf. -/
def Res (c : Context) (R : Regs) (D : BitVec 64)
    (r : FaultRecord × AddressDescriptor × TTWState × BitVec 64) : Prop :=
  r.2.2.2 = S2FetchFrame.decoded c.wp.ee D ∧ r.1.statuscode = .Fault_None ∧ r.1.level = 3 ∧
  ∃ (cur : TTWState) (m : Bool), cur.level = 3 ∧ cur.baseaddress.paspace = .PAS_NonSecure ∧
    cur.permissions.ap_table = 0#2 ∧ cur.permissions.uxn_table = 0#1 ∧
    S1LeafShape.Shape c.wp cur (S2FetchFrame.decoded c.wp.ee D) r.2.2.1 ∧
    LeafValue .Regime_EL20 cur m c.wp (S2FetchFrame.decoded c.wp.ee D) r.2.2.1 R

def PostR (c : Context) (s : State) (D : BitVec 64)
    (r : FaultRecord × AddressDescriptor × TTWState × BitVec 64) (t : State) : Prop :=
  t.regs = s.regs ∧ t.mem = s.mem ∧ Res c s.regs D r

theorem epd20_eq (va : BitVec 64) (hvr : AArch64_GetVARange va = .VARange_LOWER) (s : State) :
    AArch64_S1EPD .Regime_EL20 va s =
      .ok (_get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2)) s := by
  simp [AArch64_S1EPD, hvr, HasUnprivileged, ArmFull.assert, PreSail.assert, readReg,
    PreSail.readReg_apply, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  rfl

/-- M1-a: result of the actual AArch64_S1Walk (EL2&0, lower range) along a
    Walk20 path from the actual root slot to a level-3 leaf. -/
theorem walk_result (c : Context) (f : FaultRecord) (s : State) (n : Nat) {L : Int}
    {S : FullAddress} {D : BitVec 64}
    (hEL20 : c.regime = .Regime_EL20) (hHaft : c.wp.haft = 0#1)
    (hvr : AArch64_GetVARange c.va = .VARange_LOWER)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false)
    (hTx : c.wp.txsz = 16#6) (hStart : c.startlevel = 0)
    (hRootIn : (!is_zero_subrange (S1EntryRoot.slot c.wp s.regs c.regime c.va).address
      55 (S2PhysicalSizeFrame.value c.wp.ps)) = false)
    (hWalk : Walk20 c.wp c.va s.mem n 0 (S1EntryRoot.slot c.wp s.regs c.regime c.va) L S D)
    (hL3 : L = 3)
    (hContig : S1Contiguous.bit (S2FetchFrame.decoded c.wp.ee D) = 0#1)
    (hAF : BitVec.join1 [BitVec.access (S2FetchFrame.decoded c.wp.ee D) 10] = 1#1)
    (hOA : ∀ v : TTWState, v.level = 3 →
      v.baseaddress.address = S1LeafBaseFrame.base (S2FetchFrame.decoded c.wp.ee D) 3 →
      (!is_zero_subrange (S1StageOA.address c.va v).address 55
        (S2PhysicalSizeFrame.value c.wp.ps)) = false) :
    ∃ r t, AArch64_S1Walk f c.wp c.va c.regime c.acc 64 s = .ok r t ∧ PostR c s D r t := by
  rw [S1WalkSource.named.equation, S1WalkTailSource.equation]
  unfold S1WalkTailSource.withTail
  apply run_wp
  apply bind_normal_me _ _ s _ _ (S1EntryDraws.bool_draw 1591)
  intro a64 t1 hf1
  apply bind_normal_me _ _ t1 _ _ (S1EntryDraws.bool_draw 1592)
  intro aligned t2 hf2
  apply bind_normal_me _ _ t2 _ _ (S1EntryDraws.context_draw 1593)
  intro ctx t3 hf3
  apply bind_normal_me _ _ t3 _ _ (S1EntryDraws.record_draw 1594)
  intro entry t4 hf4
  have hf14 := frame_trans (frame_trans (frame_trans hf1 hf2) hf3) hf4
  have hc : t4.regs.bank_Bool .__tlb_enabled = false := by rw [hf14.1]; exact hCache
  have hread : (readReg ArmFull.Register.__tlb_enabled : SailM Bool) t4 = .ok false t4 := by
    change EStateM.Result.ok (t4.regs.bank_Bool .__tlb_enabled) t4 = .ok false t4
    rw [hc]
  apply bind_lift_eq _ _ t4 t4 false _ _ hread
  simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  have hup : HasUnprivileged c.regime = true := by
    rcases c.regimes with h | h <;> rw [h] <;> rfl
  simp only [hup, ↓reduceIte]
  apply bind_wp
  refine ⟨.ok false, t4, ?_, ?_⟩
  · have he := epd20_eq c.va hvr t4
    have hE : _get_TCR_EL2_Type_EPD0 (t4.regs.bank_BitVec_64 .TCR_EL2) = 0#1 := by
      rw [hf14.1]; exact hEPD0
    rw [hEL20]
    simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.lift, Pure.pure,
      ExceptT.pure, EStateM.bind, EStateM.pure, EStateM.map, Functor.map, liftM,
      MonadLiftT.monadLift, MonadLift.monadLift, he, hE]
  simp only [S1EntryWP.Post]
  rw [c.ss]
  rcases S1EntryRoot.total c.wp c.va c.regime t4 c.regimes c.d128 c.ds c.tg hTx
    (by rw [hf14.1]; exact hReady.el3A64) (by rw [hf14.1]; exact hReady.noEL3A32) with
    ⟨w, t6, hinit, hf6, hs, hb⟩
  apply bind_lift_eq _ _ t4 t6 w _ _ hinit
  have hf16 := frame_trans hf14 hf6
  apply bind_normal_me _ _ t6 _ _ (S1EntryDraws.bits_draw 1595)
  intro d t7 hf7
  have hf17 := frame_trans hf16 hf7
  apply bind_normal_me _ _ t7 _ _ (S1EntryDraws.address_draw 1596)
  intro initialAddress t8 hf8
  have hf18 := frame_trans hf17 hf8
  have hmec : AArch64_TTWalkMECID c.wp.emec c.regime .SS_NonSecure t8 =
      .ok DEFAULT_MECID t8 := by rw [S1EntryCallees.mecid_eq]; rfl
  apply bind_lift_eq _ _ t8 t8 DEFAULT_MECID _ _ hmec
  apply bind_lift_normal _ _ t8 _ _ (S1EntryCallees.dcache_normal c.regime c.regimes)
  intro enabled t9 hf9
  have hf19 := frame_trans hf18 hf9
  apply bind_normal_me _ _ t9 _ _
  · apply S1NormalME.normal_ite
    · intro hdisabled
      apply S1NormalME.normal_bind
      · exact S1NormalME.lift_normal _ _ S1EntryCalleesExtra.normalnc_normal
      · intro attrs
        exact S1NormalME.normal_pure _ _
    · intro henabled
      exact S1NormalME.normal_pure _ _
  · intro walkaddr t10 hf10
    have hf110 := frame_trans hf19 hf10
    have hv : _get_HCR_EL2_Type_VM (t10.regs.bank_BitVec_64 .HCR_EL2) = 0#1 := by
      rw [hf110.1, hReady.config.hHCR]
      exact c.vm
    apply S1EntryShare.bind_disabled c.regime _ t10 _ _ hv
    intro t11 hf11
    have hf111 := frame_trans hf110 hf11
    apply bind_normal_me _ _ t11 _ _ (S1EntryDraws.type_draw 1597)
    intro typ t12 hf12
    have hf112 := frame_trans hf111 hf12
    have hp := hs.2.2.1
    have hb0 : w.baseaddress.address = S1EntryRoot.base c.wp s.regs c.regime c.va := by
      rw [hf14.1] at hb
      exact hb
    have hbase : w.baseaddress =
        {address := S1EntryRoot.base c.wp s.regs c.regime c.va, paspace := .PAS_NonSecure} := by
      cases he : w.baseaddress with
      | mk pas addr =>
        simp only [he] at hp hb0
        simp only [he, hp, hb0]
    rcases S1InitialEntryAddress.total c.wp c.va w.baseaddress t12 c.d128 c.tg hTx with
      ⟨t13, ha, hf13⟩
    have ha0 : AArch64_S1SLTTEntryAddress w.level c.wp c.va w.baseaddress t12 =
        .ok (S1EntryRoot.slot c.wp s.regs c.regime c.va) t13 := by
      simpa only [hs.1, hbase, S1EntryRoot.slot] using ha
    apply bind_lift_eq _ _ t12 t13 (S1EntryRoot.slot c.wp s.regs c.regime c.va) _ _ ha0
    have hf113 := frame_trans hf112 hf13
    rcases S2OAFrame.total (S1EntryRoot.slot c.wp s.regs c.regime c.va).address c.wp.ps t13
      (by rw [hf113.1]; exact hReady.pa) with ⟨t14, hrange, hr14, hm14, he14⟩
    have hrange0 : AArch64_OAOutOfRange
        (S1EntryRoot.slot c.wp s.regs c.regime c.va).address c.wp.d128 c.wp.ps c.wp.tgx t13 =
        .ok (!is_zero_subrange (S1EntryRoot.slot c.wp s.regs c.regime c.va).address
          55 (S2PhysicalSizeFrame.value c.wp.ps)) t14 := by
      simpa only [c.d128, c.tg] using hrange
    apply bind_lift_eq _ _ t13 t14 _ _ _ hrange0
    have hf114 := frame_trans hf113 ⟨hr14, hm14, he14⟩
    have hout : (!is_zero_subrange (S1EntryRoot.slot c.wp s.regs c.regime c.va).address
        55 (S2PhysicalSizeFrame.value c.wp.ps)) = false := hRootIn
    rw [hout]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hc14 : t14.regs.bank_Bool .__tlb_enabled = false := by
      rw [hf114.1]; exact hCache
    have hwalk14 : Walk20 c.wp c.va t14.mem n w.level
        (S1EntryRoot.slot c.wp s.regs c.regime c.va) L S D := by
      rw [hf114.2.1, hs.1]; exact hWalk
    rcases tail_result c hEL20 hHaft ctx entry aligned (S1EntryRoot.slot c.wp s.regs c.regime c.va)
      d typ f a64 false 0#2
      {walkaddr with memattrs := {walkaddr.memattrs with
        shareability := EffectiveShareability walkaddr.memattrs}, tlbcontext := ctx}
      w t14 (hReady.of_regs hf114.1) hFault hp hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1
      hc14 hwalk14 hL3 hContig hAF hOA with
      ⟨fr, wa, next, u, hrun, h1, h2, h3, hr, hm⟩
    have posteq : PostR c t14 D = PostR c s D := by
      funext r v
      simp only [PostR, Res, hf114.1, hf114.2.1]
    rw [← posteq]
    simpa only [hStart, hs.1] using
      (S1EntryWP.of_run _ t14 u (fr, wa, next, S2FetchFrame.decoded c.wp.ee D) (PostR c t14 D)
        hrun ⟨hr, hm, rfl, h1, h2, h3⟩)


#print axioms walk_result
end ArmCert.Eval.M1a
