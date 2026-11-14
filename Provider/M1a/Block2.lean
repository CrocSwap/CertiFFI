import M1a.J3Pages
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a.B2
abbrev State := SequentialState Regs oracleChoiceSource
open S1OuterSetup S1Normality ArmCert.Eval.M1a

/- Level-2 (2 MB block) leaves for the EL2&0 walk (a design decision(b);). -/

drive_spec blnt_native, blnt_eq : fun (d : BitVec 64) (s : SequentialState Regs oracleChoiceSource) =>
  AArch64_BlocknTFaults 0#1 d s

/-- The block nT check does not fault for a descriptor with nT (bit 16) = 0 (d128 = 0; Linux
    never sets nT). With FEAT_BBM absent it is false regardless. -/
theorem blocknT_false (d : BitVec 64) (hnT : BitVec.join1 [BitVec.access d 16] = 0#1) (s : State) :
    ∃ t, AArch64_BlocknTFaults 0#1 d s = .ok false t ∧ Frame s t := by
  rw [blnt_eq]
  observe_simp [Frame, blnt_native]

#print axioms blocknT_false

/-- suffix_ev at a level-2 block leaf: the block nT check runs and returns false. -/
theorem suffix_ev2 (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (ctx : TLBContext) (entry : TLBRecord)
    (aligned : Bool) (slot : FullAddress) (d : BitVec 64) (f : FaultRecord)
    (a64 mro : Bool) (skl : BitVec 2) (walkaddr : AddressDescriptor) (w : TTWState)
    (s : State)
    (hd : wp.d128 = 0#1) (htg : wp.tgx = .TGx_4KB)
    (hl : w.level = 2) (hc : w.contiguous = 0#1)
    (hpas : w.baseaddress.paspace = .PAS_NonSecure)
    (hf : f.statuscode = .Fault_None)
    (hAF : BitVec.join1 [BitVec.access d 10] = 1#1)
    (hnT : BitVec.join1 [BitVec.access d 16] = 0#1)
    (hOA : (!is_zero_subrange (S1StageOA.address va w).address 55
      (S2PhysicalSizeFrame.value wp.ps)) = false)
    (hPA : s.regs.bank_Int .__supported_pa_size = 48)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false) :
    ∃ t : State,
      S1WalkSuffixSource.suffix wp va regime acc 64 ctx entry
        (aligned, slot, d, .DescriptorType_Leaf, f, a64, mro, skl, walkaddr, w) s =
        .ok (.ok (f, walkaddr, w, d)) t ∧ t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rcases S1StageOA.total va w s (by omega) with ⟨t1, hoa, hf1⟩
  rcases blocknT_false d hnT t1 with ⟨tb, hbn, hfb⟩
  have hfb1 := ArmCert.Eval.JointSAT.Regime.frame_trans hf1 hfb
  rcases S2OAFrame.total (S1StageOA.address va w).address wp.ps tb (by rw [hfb1.1]; exact hPA) with
    ⟨t2, hrange, hr2, hm2, he2⟩
  have hc2 : t2.regs.bank_Bool .__tlb_enabled = false := by rw [hr2, hfb1.1]; exact hCache
  have hguard := S1CacheGuard.disabled d f t2 hc2
  have hamec := ArmCert.Eval.M1a.amec_eq wp .PAS_NonSecure regime d hd tb
  have hAF0 : ¬ (BitVec.join1 [BitVec.access d 10] = 0#1) := by rw [hAF]; simp
  have hR : (PASpace.PAS_NonSecure == PASpace.PAS_Realm) = false := by decide
  have hFin : ((2 : Int) < FINAL_LEVEL) := by decide
  have hLL : (DescriptorType.DescriptorType_Leaf == DescriptorType.DescriptorType_Leaf) = true := rfl
  have hNo : ((Fault.Fault_None : Fault) != Fault.Fault_None) = false := by decide
  refine ⟨t2, ?_, hr2.trans hfb1.1, hm2.trans hfb1.2.1, he2.trans hfb1.2.2⟩
  unfold S1WalkSuffixSource.suffix
  simp only [hd, htg, hl, hc]
  simp [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure, ExceptT.lift,
    Pure.pure, EStateM.bind, EStateM.pure, EStateM.map, Functor.map, liftM,
    MonadLiftT.monadLift, MonadLift.monadLift, hoa, hbn, hrange, hOA, hguard, hf, hAF0,
    hamec, S1WalkChecks.amec, hpas, hR, hFin, hLL, hNo, hd, ArmFull.assert, PreSail.assert]

#print axioms suffix_ev2
open ArmCert.Eval.M1a.WEv

/-- Res at a level-2 block leaf (Entry20.Res with level 2). -/
def Res2 (c : Context) (R : Regs) (D : BitVec 64)
    (r : FaultRecord × AddressDescriptor × TTWState × BitVec 64) : Prop :=
  r.2.2.2 = S2FetchFrame.decoded c.wp.ee D ∧ r.1.statuscode = .Fault_None ∧ r.1.level = 2 ∧
  ∃ (cur : TTWState) (m : Bool), cur.level = 2 ∧ cur.baseaddress.paspace = .PAS_NonSecure ∧
    cur.permissions.ap_table = 0#2 ∧ cur.permissions.uxn_table = 0#1 ∧
    S1LeafShape.Shape c.wp cur (S2FetchFrame.decoded c.wp.ee D) r.2.2.1 ∧
    LeafValue .Regime_EL20 cur m c.wp (S2FetchFrame.decoded c.wp.ee D) r.2.2.1 R

def PostR2 (c : Context) (s : State) (D : BitVec 64)
    (r : FaultRecord × AddressDescriptor × TTWState × BitVec 64) (t : State) : Prop :=
  t.regs = s.regs ∧ t.mem = s.mem ∧ Res2 c s.regs D r

theorem tail_ev2 (c : Context) (hEL20 : c.regime = .Regime_EL20) (hHaft : c.wp.haft = 0#1)
    (ctx : TLBContext) (entry : TLBRecord) (aligned : Bool) (descaddr : FullAddress)
    (d : BitVec 64) (typ : DescriptorType) (f : FaultRecord) (a64 mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (w : TTWState) (s : State) {n : Nat} {L : Int}
    {S : FullAddress} {D : BitVec 64}
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hPAS : w.baseaddress.paspace = .PAS_NonSecure)
    (hap : w.permissions.ap_table = 0#2) (hux : w.permissions.uxn_table = 0#1)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false)
    (hWalk : Walk20 c.wp c.va s.mem n w.level descaddr L S D)
    (hL2 : L = 2)
    (hContig : S1Contiguous.bit (S2FetchFrame.decoded c.wp.ee D) = 0#1)
    (hAF : BitVec.join1 [BitVec.access (S2FetchFrame.decoded c.wp.ee D) 10] = 1#1)
    (hnT : BitVec.join1 [BitVec.access (S2FetchFrame.decoded c.wp.ee D) 16] = 0#1)
    (hOA : ∀ v : TTWState, v.level = 2 →
      v.baseaddress.address = S1LeafBaseFrame.base (S2FetchFrame.decoded c.wp.ee D) 2 →
      (!is_zero_subrange (S1StageOA.address c.va v).address 55
        (S2PhysicalSizeFrame.value c.wp.ps)) = false) :
    ∃ (fr : FaultRecord) (wa : AddressDescriptor) (next : TTWState) (t : State),
      S1WalkTail.action c ctx entry aligned descaddr d typ f a64 mro skl walkaddr w s =
        .ok (fr, wa, next, S2FetchFrame.decoded c.wp.ee D) t ∧
      fr.statuscode = .Fault_None ∧ fr.level = 2 ∧
      (∃ (cur : TTWState) (m : Bool), cur.level = 2 ∧
        cur.baseaddress.paspace = .PAS_NonSecure ∧
        cur.permissions.ap_table = 0#2 ∧ cur.permissions.uxn_table = 0#1 ∧
        S1LeafShape.Shape c.wp cur (S2FetchFrame.decoded c.wp.ee D) next ∧
        LeafValue .Regime_EL20 cur m c.wp (S2FetchFrame.decoded c.wp.ee D) next s.regs) ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧
      ∃ W, t.events = s.events ++ W ∧ ReadsAlong c.wp c.va s.mem n w.level descaddr W := by
  rcases trace20_ev c hEL20 hHaft hWalk s hReady rfl aligned d typ f a64 mro skl walkaddr w rfl
    hFault hPAS hap hux with ⟨y, t, htrace, hr, hm, hend, W, hW, hRA⟩
  have hlen := ArmCert.Eval.M1a.walk20_length hWalk
  have hloop : S1WalkSource.named.loop0 c.wp c.va c.regime c.acc 64 a64 aligned f w c.startlevel
      d skl walkaddr mro typ descaddr s = .ok (.ok y) t := by
    simpa only [S1WalkSource.named.loop0, stop] using
      S2Loop.execute htrace 1048576 (by omega)
  rcases y with ⟨aligned', slot', d', typ', f', a64', mro', skl', walkaddr', next⟩
  rcases hend with ⟨hslot, hd', htyp, hfs, hfl, cur, hcl, hcp, hca, hcu, hshape, hval⟩
  subst hd' htyp
  rcases hshape with ⟨hist, hlev, hbase, hnpas, hcontig, _⟩
  have hnl : next.level = 2 := by rw [hlev, hcl, hL2]
  have hnc : next.contiguous = 0#1 := by
    rw [hcontig, hContig]; split <;> rfl
  rcases suffix_ev2 c.wp c.va c.regime c.acc ctx entry aligned' slot'
    (S2FetchFrame.decoded c.wp.ee D) f' a64' mro' skl' walkaddr' next t c.d128 c.tg hnl hnc hnpas
    hfs hAF hnT (hOA next hnl (by rw [hbase, hcl, hL2]))
    (by rw [hr]; exact hReady.pa) (by rw [hr]; exact hCache) with ⟨u, hsuf, hr2, hm2, he2⟩
  refine ⟨f', walkaddr', next, u, ?_, hfs, by rw [hfl, hL2], ⟨cur, mro', by rw [hcl, hL2], hcp,
    hca, hcu, ⟨hist, hlev, hbase, hnpas, hcontig, by assumption⟩, hval⟩, hr2.trans hr, hm2.trans hm,
    W, by rw [he2, hW], hRA⟩
  simp [S1WalkTail.action, S1WalkTailSource.tail, SailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, Bind.bind, ExceptT.bind, ExceptT.mk,
    ExceptT.run, ExceptT.bindCont, EStateM.bind, Pure.pure, EStateM.pure, hloop, hsuf]



open S1EntryWP S1Normality in
theorem walk_result_ev2 (c : Context) (f : FaultRecord) (s : State) (n : Nat) {L : Int}
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
    (hL2 : L = 2)
    (hContig : S1Contiguous.bit (S2FetchFrame.decoded c.wp.ee D) = 0#1)
    (hAF : BitVec.join1 [BitVec.access (S2FetchFrame.decoded c.wp.ee D) 10] = 1#1)
    (hnT : BitVec.join1 [BitVec.access (S2FetchFrame.decoded c.wp.ee D) 16] = 0#1)
    (hOA : ∀ v : TTWState, v.level = 2 →
      v.baseaddress.address = S1LeafBaseFrame.base (S2FetchFrame.decoded c.wp.ee D) 2 →
      (!is_zero_subrange (S1StageOA.address c.va v).address 55
        (S2PhysicalSizeFrame.value c.wp.ps)) = false) :
    ∃ r t, AArch64_S1Walk f c.wp c.va c.regime c.acc 64 s = .ok r t ∧
      (PostR2 c s D r t ∧ ∃ W, t.events = s.events ++ W ∧ ReadsAlong c.wp c.va s.mem n 0 (S1EntryRoot.slot c.wp s.regs c.regime c.va) W) := by
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
  · have he := ArmCert.Eval.M1a.epd20_eq c.va hvr t4
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
    rcases tail_ev2 c hEL20 hHaft ctx entry aligned (S1EntryRoot.slot c.wp s.regs c.regime c.va)
      d typ f a64 false 0#2
      {walkaddr with memattrs := {walkaddr.memattrs with
        shareability := EffectiveShareability walkaddr.memattrs}, tlbcontext := ctx}
      w t14 (hReady.of_regs hf114.1) hFault hp hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1
      hc14 hwalk14 hL2 hContig hAF hnT hOA with
      ⟨fr, wa, next, u, hrun, h1, h2, h3, hr, hm, W, hW, hRA⟩
    have posteq : (fun r v => PostR2 c t14 D r v ∧ ∃ W, v.events = t14.events ++ W ∧
        ReadsAlong c.wp c.va t14.mem n w.level (S1EntryRoot.slot c.wp s.regs c.regime c.va) W) =
        (fun r v => PostR2 c s D r v ∧ ∃ W, v.events = s.events ++ W ∧
        ReadsAlong c.wp c.va s.mem n 0 (S1EntryRoot.slot c.wp s.regs c.regime c.va) W) := by
      funext r v
      simp only [PostR2, Res2, hf114.1, hf114.2.1, hf114.2.2, hs.1, hStart]
    rw [← posteq]
    simpa only [hStart, hs.1] using
      (S1EntryWP.of_run _ t14 u (fr, wa, next, S2FetchFrame.decoded c.wp.ee D)
        (fun r v => PostR2 c t14 D r v ∧ ∃ W, v.events = t14.events ++ W ∧
          ReadsAlong c.wp c.va t14.mem n w.level (S1EntryRoot.slot c.wp s.regs c.regime c.va) W)
        hrun ⟨⟨hr, hm, rfl, h1, h2, h3⟩, W, hW, hRA⟩)




#print axioms tail_ev2
#print axioms walk_result_ev2
open S1LogicalReference in
/-- of_path20 for a leaf at any level L (here used with L = 2, 2 MB blocks). -/
theorem of_path20L (wp : S1TTWParams) (va : BitVec 64) (mem : S1ByteMemory.Memory)
    (observe : Observation)
    (available : Available observe (fun p => S2TableRAM.OrdinaryRAM p.address))
    (realizes : Realizes observe (wp.ee == 1#1) (wp.pie == 1#1)
      (wp.ha == 1#1) (wp.hd == 1#1) (fun a => mem[a]?))
    (identity : S1EntryPathSlots.Identity observe)
    (htab : ∀ l p v d, observe l p v → BytesAt (wp.ee == 1#1) (fun a => mem[a]?) p d →
      ∀ level : Nat, descriptorKind level v.stable = .ok .table → TablePermsZero d)
    {level bits : Nat} {base : BitVec 48} {result : PathEnd}
    (path : Path observe (S2PhysicalSizeFrame.value wp.ps).toNat va level bits base result) :
    ∀ (L slotL : Nat) (physL : FullAddress) (vL : S1DescriptorPIE.View 64),
      result = .leaf L slotL physL vL → bits = 9 →
      ∀ slot : FullAddress, slot.address.toNat = entryAddress base va level bits →
      ∃ (n : Nat) (S : FullAddress) (D : BitVec 64),
        Walk20 wp va mem n (level : Int) slot (L : Int) S D ∧
        S.address.toNat = physL.address.toNat ∧
        BytesAt (wp.ee == 1#1) (fun a => mem[a]?) physL (S2FetchFrame.decoded wp.ee D) := by
  induction path with
  | invalid => intro _ _ _ _ hres; cases hres
  | range => intro _ _ _ _ hres; cases hres
  | leaf lv bs b physical v hl aligned present kind =>
    intro L slotL physL vL hres _ slot hslot
    cases hres
    rcases realizes _ physical v present with ⟨d, hb, hv⟩
    have ha := available _ physical v present
    have he : slot.address = physical.address :=
      BitVec.eq_of_toNat_eq (hslot.trans (identity _ physical v present).symm)
    have hdesc : S2ByteMemory.DescAt mem slot.address.toNat (S2Endian.encode wp.ee d) := by
      rw [he]; exact (S1ReferenceEncoding.bytes_iff wp.ee mem physical d).mp hb
    have hk := S1ReferenceKind.view_kind _ _ _ d v hv lv (by omega)
    have hleaf : S1DecodeFacts.classify (S2FetchFrame.decoded wp.ee (S2Endian.encode wp.ee d))
        ((lv : Nat) : Int) = .DescriptorType_Leaf := by
      rw [decoded_encode]
      cases h : S1DecodeFacts.classify d ((lv : Nat) : Int) <;> simp_all
    refine ⟨1, slot, S2Endian.encode wp.ee d, Walk20.leaf ⟨by omega, by omega⟩ (by rw [he]; exact ha.2.2)
      hdesc hleaf, by rw [he], by rw [decoded_encode]; exact hb⟩
  | table lv bs b physical v res hl aligned present kind inRange next ih =>
    intro L slotL physL vL hres hbits slot hslot
    rcases realizes _ physical v present with ⟨d, hb, hv⟩
    have ha := available _ physical v present
    have he : slot.address = physical.address :=
      BitVec.eq_of_toNat_eq (hslot.trans (identity _ physical v present).symm)
    have hdesc : S2ByteMemory.DescAt mem slot.address.toNat (S2Endian.encode wp.ee d) := by
      rw [he]; exact (S1ReferenceEncoding.bytes_iff wp.ee mem physical d).mp hb
    have hk := S1ReferenceKind.view_kind _ _ _ d v hv lv (by omega)
    have htable : S1DecodeFacts.classify (S2FetchFrame.decoded wp.ee (S2Endian.encode wp.ee d))
        (lv : Int) = .DescriptorType_Table := by
      rw [decoded_encode]
      cases h : S1DecodeFacts.classify d (lv : Int) <;> simp_all
    have hn := S1EntryNextGeometry.next_slot wp d va lv hl
    rw [show S1ResourcePath.view wp d = v from hv] at hn
    rcases ih L slotL physL vL hres rfl (S1ResourcePath.nextSlot va (lv : Int) d) hn with
      ⟨n, S, D, hrest, hS, hbytes⟩
    refine ⟨n + 1, S, D, ?_, hS, hbytes⟩
    rw [show S2FetchFrame.decoded wp.ee (S2Endian.encode wp.ee d) = d from decoded_encode _ _] at htable
    refine Walk20.table ⟨by omega, by omega⟩ (by rw [he]; exact ha.2.2) hdesc
      (by rw [decoded_encode]; exact htable) ?_ ?_ ?_
    · rw [decoded_encode]
      apply (S1EntryRangeGeometry.in_range wp _).mpr
      rw [hn]; exact inRange
    · rw [decoded_encode]; exact htab _ physical v d present hb lv kind
    · rw [decoded_encode]
      simpa only [Int.natCast_add, Int.natCast_one] using hrest

#print axioms of_path20L
open S1LogicalReference in
theorem walk_result_path_ev2 (c : Context) (f : FaultRecord) (s : State)
    (hEL20 : c.regime = .Regime_EL20) (hHaft : c.wp.haft = 0#1)
    (hvr : AArch64_GetVARange c.va = .VARange_LOWER)
    (hEPD0 : _get_TCR_EL2_Type_EPD0 (s.regs.bank_BitVec_64 .TCR_EL2) = 0#1)
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false)
    (hTx : c.wp.txsz = 16#6) (hStart : c.startlevel = 0)
    (hRootIn : (!is_zero_subrange (S1EntryRoot.slot c.wp s.regs c.regime c.va).address
      55 (S2PhysicalSizeFrame.value c.wp.ps)) = false)
    (observe : Observation)
    (available : Available observe (fun p => S2TableRAM.OrdinaryRAM p.address))
    (realizes : Realizes observe (c.wp.ee == 1#1) (c.wp.pie == 1#1)
      (c.wp.ha == 1#1) (c.wp.hd == 1#1) (fun a => s.mem[a]?))
    (identity : S1EntryPathSlots.Identity observe)
    (htab : ∀ l p v d, observe l p v → BytesAt (c.wp.ee == 1#1) (fun a => s.mem[a]?) p d →
      ∀ level : Nat, descriptorKind level v.stable = .ok .table → TablePermsZero d)
    (slotL : Nat) (physL : FullAddress) (vL : S1DescriptorPIE.View 64)
    (path : Path observe (S2PhysicalSizeFrame.value c.wp.ps).toNat c.va 0 9
      ((S1EntryRoot.base c.wp s.regs c.regime c.va).setWidth 48) (.leaf 2 slotL physL vL))
    (hleaf : ∀ d, BytesAt (c.wp.ee == 1#1) (fun a => s.mem[a]?) physL d →
      S1Contiguous.bit d = 0#1 ∧ BitVec.join1 [BitVec.access d 10] = 1#1 ∧
      BitVec.join1 [BitVec.access d 16] = 0#1 ∧
      ∀ v : TTWState, v.level = 2 → v.baseaddress.address = S1LeafBaseFrame.base d 2 →
        (!is_zero_subrange (S1StageOA.address c.va v).address 55
          (S2PhysicalSizeFrame.value c.wp.ps)) = false) :
    ∃ (D : BitVec 64) (r : FaultRecord × AddressDescriptor × TTWState × BitVec 64) (t : State),
      BytesAt (c.wp.ee == 1#1) (fun a => s.mem[a]?) physL (S2FetchFrame.decoded c.wp.ee D) ∧
      AArch64_S1Walk f c.wp c.va c.regime c.acc 64 s = .ok r t ∧ PostR2 c s D r t ∧
      ∃ W, t.events = s.events ++ W ∧ W.size = 3 ∧ ReadsAlong c.wp c.va s.mem 3 0 (S1EntryRoot.slot c.wp s.regs c.regime c.va) W := by
  have hroot := S1EntryRootGeometry.root_slot c.wp s.regs c.regime c.va c.d128 c.tg hTx
  rcases of_path20L c.wp c.va s.mem observe available realizes identity htab path
    2 slotL physL vL rfl rfl (S1EntryRoot.slot c.wp s.regs c.regime c.va) hroot with
    ⟨n, S, D, hw, _, hbytes⟩
  rcases hleaf _ hbytes with ⟨hc, haf, hnT, hoa⟩
  have hn : n = 3 := by have := walk20_count hw; omega
  subst hn
  rcases walk_result_ev2 c f s 3 hEL20 hHaft hvr hEPD0 hReady hFault hCache hTx hStart hRootIn
    hw rfl hc haf hnT hoa with ⟨r, t, hr, hp, W, hW, hRA⟩
  exact ⟨D, r, t, hbytes, hr, hp, W, hW, hRA.size, hRA⟩


open ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.TB ArmCert.Eval.JointSAT in
/-- WalkFactE at a level-2 (2 MB) block leaf: PostR2 and exactly 3 AK_ttw reads. -/
def WalkFactE2 (s : State) (va : BitVec 64) (D : BitVec 64) : Prop :=
  ∀ t : State, t.regs = s.regs → t.mem = s.mem →
    ∀ (f : FaultRecord) (acc' : AccessDescriptor), f.statuscode = .Fault_None →
      acc'.ss = .SS_NonSecure →
      ∃ (wp : S1TTWParams) (u : State),
        AArch64_GetS1TTWParams .Regime_EL20 acc'.ss va t = .ok wp u ∧
        S1Normality.Frame t u ∧ EL20.Fields.Fields wp ∧ EL20.Active wp ∧
        ∀ v : State, v.regs = t.regs → v.mem = t.mem →
          ∃ (c : Context) (r : FaultRecord × AddressDescriptor × TTWState × BitVec 64)
            (w : State), c.wp = wp ∧ c.acc = acc' ∧ c.va = va ∧ c.regime = .Regime_EL20 ∧
            AArch64_S1Walk f wp va .Regime_EL20 acc' 64 v = .ok r w ∧ PostR2 c v D r w ∧
            ∃ W, w.events = v.events ++ W ∧ W.size = 3 ∧
              ReadsAlong wp va v.mem 3 0 (rootSlot s.regs va) W

open S1LogicalReference ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.TB ArmCert.Eval.JointSAT in
theorem translate_walk_path_evT2 (s : State) (h : Host20T s) (va : BitVec 64)
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
    (path : Path observe 48 va 0 9 ((rootOf s.regs va).setWidth 48) (.leaf 2 slotL physL vL))
    (D : BitVec 64) (hD : BytesAt false (fun a => s.mem[a]?) physL D)
    (hleaf : S1Contiguous.bit D = 0#1 ∧ BitVec.join1 [BitVec.access D 10] = 1#1 ∧
      BitVec.join1 [BitVec.access D 16] = 0#1 ∧
      ∀ v : TTWState, v.level = 2 → v.baseaddress.address = S1LeafBaseFrame.base D 2 →
        (!is_zero_subrange (S1StageOA.address va v).address 55 48) = false) :
    WalkFactE2 s va D := by
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
  rcases walk_result_path_ev2 c f v rfl hhaft hvr (by rw [hvs]; exact hEPD0) hR hf hv.tlb htx rfl
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
      refine ⟨hleaf.1, hleaf.2.1, hleaf.2.2.1, ?_⟩
      intro w hl hb
      rw [hpa]; exact hleaf.2.2.2 w hl hb) with ⟨D', r, w, hbytes, hw, hpost, W, hW, hWs, hRA⟩
  rw [heeB, hmemv, hdec] at hbytes
  have hDD : D' = D := bytes_unique _ _ _ _ hbytes hD
  subst hDD
  have hslot : S1EntryRoot.slot c.wp v.regs c.regime c.va = rootSlot s.regs va := by
    unfold S1EntryRoot.slot rootSlot; rw [hbase]
  rw [hslot] at hRA
  exact ⟨c, r, w, rfl, rfl, rfl, rfl, hw, hpost, W, hW, hWs, hRA⟩



#print axioms walk_result_path_ev2
#print axioms translate_walk_path_evT2
open S1LogicalReference

theorem entryIndex_block {va va' : BitVec 64} (h : va'.toNat / 2097152 = va.toNat / 2097152)
    {level : Nat} (bits : Nat) (hl : level ≤ 2) :
    entryIndex va' level bits = entryIndex va level bits := by
  unfold entryIndex
  have e1 : 12 + 9 * (3 - level) = 21 + 9 * (2 - level) := by omega
  have e : 2 ^ (12 + 9 * (3 - level)) = 2097152 * 2 ^ (9 * (2 - level)) := by
    rw [e1, Nat.pow_add]
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

theorem entryAddress_block {va va' : BitVec 64} (h : va'.toNat / 2097152 = va.toNat / 2097152)
    (base : BitVec 48) {level : Nat} (bits : Nat) (hl : level ≤ 2) :
    entryAddress base va' level bits = entryAddress base va level bits := by
  unfold entryAddress; rw [entryIndex_block h bits hl]

/-- A Path ending in a leaf at level L starts at a level ≤ L. -/
theorem path_leaf_level {observe : Observation} {paBits : Nat} {va : BitVec 64}
    {level bits : Nat} {base : BitVec 48} {result : PathEnd}
    (p : Path observe paBits va level bits base result) :
    ∀ L sl ph v, result = .leaf L sl ph v → level ≤ L := by
  induction p with
  | invalid => intro _ _ _ _ h; cases h
  | range => intro _ _ _ _ h; cases h
  | leaf => intro _ _ _ _ h; cases h; exact Nat.le_refl _
  | table level bits base physical view result hl aligned present kind inRange next ih =>
    intro L sl ph v h
    have := ih L sl ph v h
    omega

/-- A Path to a level-2 leaf for va is one for every va' in the same 2 MB block. -/
theorem path_block {observe : Observation} {paBits : Nat} {va va' : BitVec 64}
    (h : va'.toNat / 2097152 = va.toNat / 2097152) {level bits : Nat} {base : BitVec 48}
    {result : PathEnd} (p : Path observe paBits va level bits base result) :
    ∀ sl ph v, result = .leaf 2 sl ph v → Path observe paBits va' level bits base result := by
  induction p with
  | invalid => intro _ _ _ hr; cases hr
  | range => intro _ _ _ hr; cases hr
  | leaf level bits base physical view hl aligned present kind =>
    intro sl ph v hr
    have hl2 : level = 2 := by cases hr; rfl
    have e := entryAddress_block (level := level) h base bits (by omega)
    rw [← e] at aligned present
    rw [← e]
    exact .leaf level bits base physical view hl aligned present kind
  | table level bits base physical view result hl aligned present kind inRange next ih =>
    intro sl ph v hr
    have hlv := path_leaf_level next 2 sl ph v hr
    rw [← entryAddress_block (level := level) h base bits (by omega)] at aligned present
    rw [← entryAddress_block (level := level + 1) h (childBase view) 9 (by omega)] at inRange
    exact .table level bits base physical view result hl aligned present kind inRange
      (ih sl ph v hr)

theorem testBit_block {va va' : BitVec 64} (h : va'.toNat / 2097152 = va.toNat / 2097152)
    (i : Nat) (hi : 21 ≤ i) : va'.getLsbD i = va.getLsbD i := by
  have key : ∀ x : Nat, x.testBit i = (x / 2097152).testBit (i - 21) := by
    intro x
    rw [show (2097152 : Nat) = 2 ^ 21 from rfl, Nat.testBit_div_two_pow]
    congr 1; omega
  simp only [BitVec.getLsbD]
  rw [key, key, h]

theorem varange_block {va va' : BitVec 64} (h : va'.toNat / 2097152 = va.toNat / 2097152) :
    AArch64_GetVARange va' = AArch64_GetVARange va := by
  have hb := testBit_block h 55 (by omega)
  have hb' : va'[55]! = va[55]! := by
    first | exact hb | (simp only [BitVec.getElem!_eq_getLsbD]; exact hb) | simpa using hb
  unfold AArch64_GetVARange
  simp only [BitVec.access]
  exact congrArg (fun b : Bool => if (BitVec.setWidth 1 (BitVec.join1 [BitVec.ofBool b]) == 0#1) = true
    then VARange.VARange_LOWER else VARange.VARange_UPPER) hb'

theorem rootSlot_block {va va' : BitVec 64} (h : va'.toNat / 2097152 = va.toNat / 2097152)
    (r : Regs) : ArmCert.Eval.M1a.TWP.rootSlot r va' = ArmCert.Eval.M1a.TWP.rootSlot r va := by
  have hr : AArch64_GetVARange va' = AArch64_GetVARange va := varange_block h
  have hx : va'.extractLsb' 39 9 = va.extractLsb' 39 9 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact testBit_block h (39 + i) (by omega)
  unfold ArmCert.Eval.M1a.TWP.rootSlot S1InitialEntryAddress.address ArmCert.Eval.M1a.TWP.rootOf
    S1EntryRoot.word
  simp only [hr, hx]

open S1LogicalReference ArmCert.Eval.M1a.TWP ArmCert.Eval.M1a.TB ArmCert.Eval.JointSAT in
/-- translate_walk_path_evT2 for every VA of the 2 MB block (only the leaf OA check per va'). -/
theorem translate_walk_path_evT2_block (s : State) (h : Host20T s) (va : BitVec 64)
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
    (path : Path observe 48 va 0 9 ((rootOf s.regs va).setWidth 48) (.leaf 2 slotL physL vL))
    (D : BitVec 64) (hD : BytesAt false (fun a => s.mem[a]?) physL D)
    (hleaf : S1Contiguous.bit D = 0#1 ∧ BitVec.join1 [BitVec.access D 10] = 1#1 ∧
      BitVec.join1 [BitVec.access D 16] = 0#1 ∧
      ∀ v : TTWState, v.level = 2 → v.baseaddress.address = S1LeafBaseFrame.base D 2 →
        (!is_zero_subrange (S1StageOA.address va v).address 55 48) = false) :
    ∀ va' : BitVec 64, va'.toNat / 2097152 = va.toNat / 2097152 →
      (∀ v : TTWState, v.level = 2 → v.baseaddress.address = S1LeafBaseFrame.base D 2 →
        (!is_zero_subrange (S1StageOA.address va' v).address 55 48) = false) →
      WalkFactE2 s va' D  := by
  intro va' hblk hoa'
  have hvr' : AArch64_GetVARange va' = .VARange_LOWER := by rw [varange_block hblk]; exact hvr
  have hRoot' : (!is_zero_subrange (rootSlot s.regs va').address 55 48) = false := by
    rw [rootSlot_block hblk]; exact hRootIn
  have hroot : rootOf s.regs va' = rootOf s.regs va := by
    unfold rootOf S1EntryRoot.word; simp only [varange_block hblk]
  exact translate_walk_path_evT2 s h va' hvr' hEPD0 hRoot' observe available realizes identity htab
    slotL physL vL (by rw [hroot]; exact path_block hblk path slotL physL vL rfl) D hD
    ⟨hleaf.1, hleaf.2.1, hleaf.2.2.1, hoa'⟩

#print axioms path_block
#print axioms translate_walk_path_evT2_block
end ArmCert.Eval.M1a.B2
