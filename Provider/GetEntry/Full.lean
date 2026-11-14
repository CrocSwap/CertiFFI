import GetEntry.Draws
import GetEntry.Share
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1FullEntry
open S1OuterSetup S1EntryWP
abbrev State := S1OuterSetup.State
abbrev Return := S1EntryTail.Return

theorem post_of_frame (c : Context) (s t : State) (r : Return) (hf : S1Normality.Frame s t) :
    S1EntryTail.Post c s r t := by
  refine ⟨hf.1, ?_⟩
  rw [hf.2.1]
  intro a ha v
  exact Iff.rfl

theorem normal_frame_wp (c : Context) (s u : State) (p : SailME Return Return)
    (hf : S1Normality.Frame s u) (hp : S1NormalME.Normal (fun _ => True) p) :
    WP p u (S1EntryTail.Post c s) (S1EntryTail.Post c s) := by
  rcases hp u trivial with ⟨r, t, hr, hft, _⟩
  exact ⟨.ok r, t, hr, post_of_frame c s t r (frame_trans hf hft)⟩

theorem total
 (c : Context) (f : FaultRecord) (s : State) (n : Nat)
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false)
    (hTx : c.wp.txsz = 16#6) (hStart : c.startlevel = 0)
    (hPath : S1ResourcePath.Slots c.wp c.va s.mem n 0
      (S1EntryRoot.slot c.wp s.regs c.regime c.va)) :
    ∃ r t, AArch64_S1Walk f c.wp c.va c.regime c.acc 64 s = .ok r t ∧
      S1EntryTail.Post c s r t := by
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
  apply bind_normal_me _ _ t4 _ _ (S1EntryDraws.epd_flag c.regime c.va c.regimes)
  intro epd t5 hf5
  have hf15 := frame_trans hf14 hf5
  cases epd with
  | true =>
    apply normal_frame_wp c s t5 _ hf15
    repeat first
      | exact S1NormalME.normal_pure _ _
      | exact S1NormalME.lift_normal _ _ S1WalkSuffix.unknown_address
      | exact S1NormalME.lift_normal _ _ S1WalkSuffix.unknown_walk
      | exact S1NormalME.lift_normal _ _ S1WalkSuffix.unknown_bits
      | apply S1NormalME.normal_bind
      | apply S1NormalME.normal_map
      | intro x
  | false =>
    rw [c.ss]
    rcases S1EntryRoot.total c.wp c.va c.regime t5 c.regimes c.d128 c.ds c.tg hTx
      (by rw [hf15.1]; exact hReady.el3A64) (by rw [hf15.1]; exact hReady.noEL3A32) with
      ⟨w, t6, hinit, hf6, hs, hb⟩
    apply bind_lift_eq _ _ t5 t6 w _ _ hinit
    have hf16 := frame_trans hf15 hf6
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
        rw [hf15.1] at hb
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
      cases hout : (!is_zero_subrange (S1EntryRoot.slot c.wp s.regs c.regime c.va).address
          55 (S2PhysicalSizeFrame.value c.wp.ps)) with
      | true =>
        simp only [Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte]
        apply normal_frame_wp c s t14 _ hf114
        repeat first
          | exact S1NormalME.normal_pure _ _
          | exact S1NormalME.lift_normal _ _ S1WalkSuffix.unknown_address
          | exact S1NormalME.lift_normal _ _ S1WalkSuffix.unknown_walk
          | exact S1NormalME.lift_normal _ _ S1WalkSuffix.unknown_bits
          | apply S1NormalME.normal_bind
          | apply S1NormalME.normal_map
          | intro x
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hpath14 : S1ResourcePath.Slots c.wp c.va t14.mem n w.level
            (S1EntryRoot.slot c.wp s.regs c.regime c.va) := by
          rw [hf114.2.1, hs.1]
          exact hPath
        have hc14 : t14.regs.bank_Bool .__tlb_enabled = false := by
          rw [hf114.1]; exact hCache
        have posteq : S1EntryTail.Post c t14 = S1EntryTail.Post c s := by
          funext r u
          simp only [S1EntryTail.Post, hf114.1, hf114.2.1]
        rw [← posteq]
        simpa only [hStart, hs.1] using
          (S1EntryTail.total c ctx entry aligned (S1EntryRoot.slot c.wp s.regs c.regime c.va)
            d typ f a64 false 0#2
            {walkaddr with memattrs := {walkaddr.memattrs with
              shareability := EffectiveShareability walkaddr.memattrs}, tlbcontext := ctx}
            w t14 n (hReady.of_regs hf114.1) hFault hp hpath14 hc14)



#print axioms total
end S1FullEntry
