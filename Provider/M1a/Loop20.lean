import M1a.Table20
import Walk.S1OuterFinite
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a
open S1OuterSetup

/-- Exact-bytes resource path for an EL2&0 walk that ends at a leaf: records the
    final level L, slot S and raw descriptor word D. -/
inductive Walk20 (wp : S1TTWParams) (va : BitVec 64) (mem : S1ResourcePath.Memory) :
    Nat → Int → FullAddress → Int → FullAddress → BitVec 64 → Prop where
  | leaf {level slot data}
      (bounds : 0 ≤ level ∧ level ≤ 3)
      (ram : S2TableRAM.OrdinaryRAM slot.address)
      (desc : S2ByteMemory.DescAt mem slot.address.toNat data)
      (hleaf : S1DecodeFacts.classify (S2FetchFrame.decoded wp.ee data) level =
        .DescriptorType_Leaf) :
      Walk20 wp va mem 1 level slot level slot data
  | table {n level slot data L S D}
      (bounds : 0 ≤ level ∧ level ≤ 3)
      (ram : S2TableRAM.OrdinaryRAM slot.address)
      (desc : S2ByteMemory.DescAt mem slot.address.toNat data)
      (htable : S1DecodeFacts.classify (S2FetchFrame.decoded wp.ee data) level =
        .DescriptorType_Table)
      (range : S1TablePrefix10.outOfRange wp
        (S1ResourcePath.nextSlot va level (S2FetchFrame.decoded wp.ee data)) = false)
      (hperm : TablePermsZero (S2FetchFrame.decoded wp.ee data))
      (rest : Walk20 wp va mem n (level + 1)
        (S1ResourcePath.nextSlot va level (S2FetchFrame.decoded wp.ee data)) L S D) :
      Walk20 wp va mem (n + 1) level slot L S D

/-- What the outer loop ends with at a leaf. -/
def LeafEnd (wp : S1TTWParams) (R : Regs) (L : Int) (S : FullAddress) (D : BitVec 64)
    (y : Vars) : Prop :=
  match (y : Bool × FullAddress × BitVec 64 × DescriptorType × FaultRecord × Bool × Bool ×
      BitVec 2 × AddressDescriptor × TTWState) with
  | (_, addr, d, typ, f, _, mro, _, _, next) =>
    addr = S ∧ d = S2FetchFrame.decoded wp.ee D ∧ typ = .DescriptorType_Leaf ∧
    f.statuscode = .Fault_None ∧ f.level = L ∧
    ∃ cur : TTWState, cur.level = L ∧ cur.baseaddress.paspace = .PAS_NonSecure ∧
      cur.permissions.ap_table = 0#2 ∧ cur.permissions.uxn_table = 0#1 ∧
      S1LeafShape.Shape wp cur (S2FetchFrame.decoded wp.ee D) next ∧
      LeafValue .Regime_EL20 cur mro wp (S2FetchFrame.decoded wp.ee D) next R

theorem trace20 (c : Context) (hEL20 : c.regime = .Regime_EL20) (hHaft : c.wp.haft = 0#1)
    {n : Nat} {level : Int} {slot : FullAddress} {L : Int} {S : FullAddress} {D : BitVec 64}
    {mem : S1ResourcePath.Memory}
    (h : Walk20 c.wp c.va mem n level slot L S D) :
    ∀ (s : State), Ready c s → s.mem = mem → ∀ (aligned : Bool) (d : BitVec 64) (typ : DescriptorType) (fault : FaultRecord)
      (a64 mro : Bool) (skl : BitVec 2) (walkaddr : AddressDescriptor) (current : TTWState),
      current.level = level → fault.statuscode = .Fault_None →
      current.baseaddress.paspace = .PAS_NonSecure →
      current.permissions.ap_table = 0#2 → current.permissions.uxn_table = 0#1 →
      ∃ (y : Vars) (t : State),
        S2Loop.Trace stop (S1WalkSource.named.body0 c.wp c.va c.regime c.acc 64 c.startlevel)
          n (aligned, slot, d, typ, fault, a64, mro, skl, walkaddr, current) s (.ok y) t ∧
        t.regs = s.regs ∧ t.mem = s.mem ∧ LeafEnd c.wp s.regs L S D y := by
  induction h with
  | @leaf lv sl data bounds ram desc hleaf =>
    intro s hReady hsm aligned d typ fault a64 mro skl walkaddr current hlv hf hpas hap hux
    rw [← hsm] at desc
    subst hlv
    rw [hEL20]
    rcases outer_leaf .Regime_EL20 (Or.inr rfl) c.wp c.va c.acc c.startlevel aligned sl d typ
      fault a64 mro skl walkaddr current c.cfg data s c.d128 c.ds c.tg c.aie c.mair hpas hf
      hReady.config c.vm c.dc c.ss hReady.el hReady.noRME hReady.a64 hReady.el3A64
      hReady.noEL3A32 ram desc hleaf with ⟨r, next, t, hrun, hr, hm, hs, hv⟩
    refine ⟨_, t, .done hrun rfl, hr, hm, rfl, rfl, rfl, by simp [hf], rfl,
      current, rfl, hpas, hap, hux, hs, hv⟩
  | @table m lv sl data L' S' D' bounds ram desc htable range hperm rest ih =>
    intro s hReady hsm aligned d typ fault a64 mro skl walkaddr current hlv hf hpas hap hux
    rw [← hsm] at desc
    subst hlv
    rcases outer_table20 c.wp c.va c.acc c.startlevel aligned sl d typ fault a64 mro skl walkaddr
      current c.cfg data s c.d128 c.ds c.tg hHaft bounds hpas hReady.pa hf
      hReady.config c.vm c.dc c.ss hReady.el hReady.noRME hReady.a64 hReady.el3A64
      hReady.noEL3A32 ram desc htable range hperm with
      ⟨r, next, t1, hrun, hr1, hm1, hnl, hnp, hna, hnu⟩
    have hReady1 : Ready c t1 := hReady.of_regs hr1
    rcases ih t1 hReady1 (hm1.trans hsm) r.aligned (S2FetchFrame.decoded c.wp.ee data) .DescriptorType_Table
      {fault with level := current.level} r.a64 r.s2fs1mro 0#2 {walkaddr with paddress := sl} next
      hnl (by simpa using hf) hnp (hna.trans hap) (hnu.trans hux) with ⟨y, u, htrace, hr2, hm2, hend⟩
    refine ⟨y, u, ?_, hr2.trans hr1, hm2.trans hm1, by rw [← hr1]; exact hend⟩
    rw [hEL20] at htrace ⊢
    exact .next hrun rfl htrace

#print axioms trace20
end ArmCert.Eval.M1a
