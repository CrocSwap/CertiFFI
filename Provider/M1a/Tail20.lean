import M1a.Suffix
import Walk.S1WalkTail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 800000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a
open S1OuterSetup

theorem walk20_length {wp : S1TTWParams} {va : BitVec 64} {mem : S1ResourcePath.Memory}
    {n : Nat} {level : Int} {slot : FullAddress} {L : Int} {S : FullAddress} {D : BitVec 64}
    (h : Walk20 wp va mem n level slot L S D) :
    0 ≤ level ∧ 0 < n ∧ n ≤ (4 - level).toNat ∧ level ≤ L ∧ L ≤ 3 := by
  induction h with
  | leaf bounds _ _ hleaf =>
    have := S1LeafShape.leaf_levels _ _ hleaf
    omega
  | table bounds _ _ _ _ _ ih => omega

/-- Result of the outer loop plus suffix (S1WalkTail.action) along a Walk20 path. -/
theorem tail_result (c : Context) (hEL20 : c.regime = .Regime_EL20) (hHaft : c.wp.haft = 0#1)
    (ctx : TLBContext) (entry : TLBRecord) (aligned : Bool) (descaddr : FullAddress)
    (d : BitVec 64) (typ : DescriptorType) (f : FaultRecord) (a64 mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (w : TTWState) (s : State) {n : Nat} {L : Int}
    {S : FullAddress} {D : BitVec 64}
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hPAS : w.baseaddress.paspace = .PAS_NonSecure)
    (hap : w.permissions.ap_table = 0#2) (hux : w.permissions.uxn_table = 0#1)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false)
    (hWalk : Walk20 c.wp c.va s.mem n w.level descaddr L S D)
    (hL3 : L = 3)
    (hContig : S1Contiguous.bit (S2FetchFrame.decoded c.wp.ee D) = 0#1)
    (hAF : BitVec.join1 [BitVec.access (S2FetchFrame.decoded c.wp.ee D) 10] = 1#1)
    (hOA : ∀ v : TTWState, v.level = 3 →
      v.baseaddress.address = S1LeafBaseFrame.base (S2FetchFrame.decoded c.wp.ee D) 3 →
      (!is_zero_subrange (S1StageOA.address c.va v).address 55
        (S2PhysicalSizeFrame.value c.wp.ps)) = false) :
    ∃ (fr : FaultRecord) (wa : AddressDescriptor) (next : TTWState) (t : State),
      S1WalkTail.action c ctx entry aligned descaddr d typ f a64 mro skl walkaddr w s =
        .ok (fr, wa, next, S2FetchFrame.decoded c.wp.ee D) t ∧
      fr.statuscode = .Fault_None ∧ fr.level = 3 ∧
      (∃ (cur : TTWState) (m : Bool), cur.level = 3 ∧
        cur.baseaddress.paspace = .PAS_NonSecure ∧
        cur.permissions.ap_table = 0#2 ∧ cur.permissions.uxn_table = 0#1 ∧
        S1LeafShape.Shape c.wp cur (S2FetchFrame.decoded c.wp.ee D) next ∧
        LeafValue .Regime_EL20 cur m c.wp (S2FetchFrame.decoded c.wp.ee D) next s.regs) ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  rcases trace20 c hEL20 hHaft hWalk s hReady rfl aligned d typ f a64 mro skl walkaddr w rfl
    hFault hPAS hap hux with ⟨y, t, htrace, hr, hm, hend⟩
  have hlen := walk20_length hWalk
  have hloop : S1WalkSource.named.loop0 c.wp c.va c.regime c.acc 64 a64 aligned f w c.startlevel
      d skl walkaddr mro typ descaddr s = .ok (.ok y) t := by
    simpa only [S1WalkSource.named.loop0, stop] using
      S2Loop.execute htrace 1048576 (by omega)
  rcases y with ⟨aligned', slot', d', typ', f', a64', mro', skl', walkaddr', next⟩
  rcases hend with ⟨hslot, hd', htyp, hfs, hfl, cur, hcl, hcp, hca, hcu, hshape, hval⟩
  subst hd' htyp
  rcases hshape with ⟨hist, hlev, hbase, hnpas, hcontig, _⟩
  have hnl : next.level = 3 := by rw [hlev, hcl, hL3]
  have hnc : next.contiguous = 0#1 := by
    rw [hcontig, hContig]; split <;> rfl
  rcases suffix_result c.wp c.va c.regime c.acc ctx entry aligned' slot'
    (S2FetchFrame.decoded c.wp.ee D) f' a64' mro' skl' walkaddr' next t c.d128 c.tg hnl hnc hnpas
    hfs hAF (hOA next hnl (by rw [hbase, hcl, hL3]))
    (by rw [hr]; exact hReady.pa) (by rw [hr]; exact hCache) with ⟨u, hsuf, hr2, hm2⟩
  refine ⟨f', walkaddr', next, u, ?_, hfs, by rw [hfl, hL3], ⟨cur, mro', by rw [hcl, hL3], hcp,
    hca, hcu, ⟨hist, hlev, hbase, hnpas, hcontig, by assumption⟩, hval⟩, hr2.trans hr, hm2.trans hm⟩
  simp [S1WalkTail.action, S1WalkTailSource.tail, SailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, Bind.bind, ExceptT.bind, ExceptT.mk,
    ExceptT.run, ExceptT.bindCont, EStateM.bind, Pure.pure, EStateM.pure, hloop, hsuf]

#print axioms walk20_length
#print axioms tail_result
end ArmCert.Eval.M1a
