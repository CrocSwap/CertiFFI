import Walk.S1Inner20
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 400000
set_option maxRecDepth 1000000
namespace ArmCert.Eval.M1a

/- M1-a.
   Result-tracking companions of the gated walk components: the leaf step
   returns its descriptor unchanged and its next walk state is a value of the
   actual AArch64_S1NextWalkStateLeaf run from a state with the walk's registers. -/

abbrev State := S1WalkInvalid.State

/-- The leaf walk state `next` is returned by the actual leaf constructor from a
    state whose registers are `R`. -/
def LeafValue (regime : Regime) (current : TTWState) (s2fs1mro : Bool)
    (wp : S1TTWParams) (d : BitVec 64) (next : TTWState) (R : Regs) : Prop :=
  ∃ s0 s1 : State, s0.regs = R ∧
    AArch64_S1NextWalkStateLeaf current s2fs1mro regime .SS_NonSecure wp d s0 = .ok next s1

theorem leaf_loop (regime : Regime) (hRegime : S1LeafBoth.Regimes regime)
    (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo) (s2fs1mro aligned : Bool)
    (descaddr : FullAddress) (d : BitVec 64) (oldType : DescriptorType)
    (fault : FaultRecord) (oldNew : BitVec 64) (a64 : Bool) (s2fault : FaultRecord)
    (skl : BitVec 2) (current : TTWState) (s : State)
    (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1) (hTG : wp.tgx = .TGx_4KB)
    (hAIE : wp.aie = 0#1) (hMAIR : wp.mair = 0x000000040044ffff#64)
    (hSS : acc.ss = .SS_NonSecure)
    (hPAS : current.baseaddress.paspace = .PAS_NonSecure)
    (hLeaf : S1DecodeFacts.classify d current.level = .DescriptorType_Leaf) :
    ∃ (next : TTWState) (t : State),
      S1WalkSource.named.loop1 wp va regime acc 64 descaddr oldType skl current
        walkaddr ti aligned d fault a64 s2fault s2fs1mro oldNew s =
        .ok (.ok (aligned, descaddr, d, .DescriptorType_Leaf, fault, d,
          a64, s2fault, skl, next)) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events ∧
      S1LeafShape.Shape wp current d next ∧
      LeafValue regime current s2fs1mro wp d next s.regs := by
  have hLevel : 1 ≤ current.level ∧ current.level ≤ 3 := by
    have := S1LeafShape.leaf_levels d current.level hLeaf
    omega
  rcases S1LeafBoth.normal_shape regime hRegime current s2fs1mro wp d hD128 hDS hTG hAIE hMAIR hPAS
    hLevel s with ⟨next, t, hn, ⟨hr, hm, he⟩, hs⟩
  rcases S1LeafBothLoop.source_loop_total regime hRegime wp va acc walkaddr ti s2fs1mro aligned
    descaddr d oldType fault oldNew a64 s2fault skl current s hD128 hDS hTG hAIE hMAIR hSS hPAS
    hLeaf with ⟨next', t', hloop, hr', hm', he', hs'⟩
  -- The loop's leaf state is the value of the same deterministic leaf constructor run.
  have hb : S1WalkSource.named.body1 wp va regime acc 64 walkaddr ti s2fs1mro
      (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s =
      .ok (.ok (aligned, descaddr, d, .DescriptorType_Leaf, fault, d,
        a64, s2fault, skl, next)) t := by
    rw [S1WalkLeaf.equation wp va regime acc walkaddr ti s2fs1mro aligned
      descaddr d oldType fault oldNew a64 s2fault skl current s hD128 hDS hTG hLeaf]
    simp [S1WalkLeaf.action, hSS, Bind.bind, Pure.pure, ExceptT.bind,
      ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift, EStateM.bind,
      EStateM.pure, Functor.map, EStateM.map, liftM, MonadLiftT.monadLift, MonadLift.monadLift, hn]
  have trace : S2Loop.Trace S1WalkInvalid.stop
      (S1WalkSource.named.body1 wp va regime acc 64 walkaddr ti s2fs1mro)
      1 (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s
      (.ok (aligned, descaddr, d, .DescriptorType_Leaf, fault, d,
        a64, s2fault, skl, next)) t := .done hb (by simp [S1WalkInvalid.stop])
  have hrun : S1WalkSource.named.loop1 wp va regime acc 64 descaddr oldType skl current
      walkaddr ti aligned d fault a64 s2fault s2fs1mro oldNew s =
      .ok (.ok (aligned, descaddr, d, .DescriptorType_Leaf, fault, d,
        a64, s2fault, skl, next)) t := by
    simpa only [S1WalkSource.named.loop1, S1WalkInvalid.stop] using
      S2Loop.execute trace 1048576 (by decide)
  exact ⟨next, t, hrun, hr, hm, he, hs, s, t, rfl, hn⟩

#print axioms leaf_loop
end ArmCert.Eval.M1a
