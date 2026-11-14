import Walk.S1WalkTable
import Walk.S1TablePrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace S1TableFault
abbrev State := S1WalkInvalid.State
def result (fault : FaultRecord) (a : AddressDescriptor) (w : TTWState)
    (d : BitVec 64) : S1WalkInvalid.Return :=
  ({fault with statuscode := .Fault_AddressSize}, a, w, d)

/- Prefix certificates are constructed by S1TablePrefix.total. The range
   hypothesis is the independent arithmetic test, not source success. -/
theorem body_total (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo)
    (s2fs1mro aligned : Bool) (descaddr : FullAddress) (d : BitVec 64)
    (oldType : DescriptorType) (fault : FaultRecord) (oldNew : BitVec 64)
    (a64 : Bool) (s2fault : FaultRecord) (skl : BitVec 2) (current : TTWState)
    (s : State) (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1)
    (hTG : wp.tgx = .TGx_4KB)
    (hTable : S1DecodeFacts.classify d current.level = .DescriptorType_Table)
    (c : S1TablePrefix.Certificate wp current d va s2fs1mro s)
    (hRange : S1TablePrefix.outOfRange wp (S1TablePrefix.address c.next va) = true) :
    ∃ (a : AddressDescriptor) (w : TTWState) (out : BitVec 64) (t : State),
      S1WalkSource.named.body1 wp va .Regime_EL20 acc 64 walkaddr ti s2fs1mro
        (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s =
        .ok (.error (.inr (result fault a w out))) t ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  rcases S1Unknowns.address_total c.state with ⟨a, t1, ha, hr1, hm1, _⟩
  rcases S1Unknowns.walkstate_total t1 with ⟨w, t2, hw, hr2, hm2, _⟩
  rcases S1Unknowns.bits_total t2 with ⟨out, t, hout, hr3, hm3, _⟩
  refine ⟨a, w, out, t, ?_, hr3.trans (hr2.trans (hr1.trans c.regs_eq)),
    hm3.trans (hm2.trans (hm1.trans c.mem_eq))⟩
  rw [S1WalkTable.equation wp va acc walkaddr ti s2fs1mro aligned descaddr d
    oldType fault oldNew a64 s2fault skl current s hD128 hDS hTG hTable]
  simp [S1WalkTable.action, result, Bind.bind, Pure.pure, Functor.map,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.lift,
    EStateM.bind, EStateM.map, EStateM.pure, liftM, MonadLiftT.monadLift,
    MonadLift.monadLift, SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
    c.next_eq, c.address_eq, c.range_eq, hRange, ha, hw, hout]
#print axioms body_total

theorem source_loop_total (wp : S1TTWParams) (va : BitVec 64) (acc : AccessDescriptor)
    (walkaddr : AddressDescriptor) (ti : TranslationInfo)
    (s2fs1mro aligned : Bool) (descaddr : FullAddress) (d : BitVec 64)
    (oldType : DescriptorType) (fault : FaultRecord) (oldNew : BitVec 64)
    (a64 : Bool) (s2fault : FaultRecord) (skl : BitVec 2) (current : TTWState)
    (s : State) (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1)
    (hTG : wp.tgx = .TGx_4KB)
    (hTable : S1DecodeFacts.classify d current.level = .DescriptorType_Table)
    (c : S1TablePrefix.Certificate wp current d va s2fs1mro s)
    (hRange : S1TablePrefix.outOfRange wp (S1TablePrefix.address c.next va) = true) :
    ∃ (a : AddressDescriptor) (w : TTWState) (out : BitVec 64) (t : State),
      S1WalkSource.named.loop1 wp va .Regime_EL20 acc 64 descaddr oldType skl current
        walkaddr ti aligned d fault a64 s2fault s2fs1mro oldNew s =
        .ok (.error (.inr (result fault a w out))) t ∧
      t.regs = s.regs ∧ t.mem = s.mem := by
  rcases body_total wp va acc walkaddr ti s2fs1mro aligned descaddr d oldType fault
    oldNew a64 s2fault skl current s hD128 hDS hTG hTable c hRange with
    ⟨a, w, out, t, hr, hregs, hmem⟩
  have trace : S2Loop.Trace S1WalkInvalid.stop
      (S1WalkSource.named.body1 wp va .Regime_EL20 acc 64 walkaddr ti s2fs1mro)
      1 (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s
      (.error (.inr (result fault a w out))) t := .returned hr
  refine ⟨a, w, out, t, ?_, hregs, hmem⟩
  simpa only [S1WalkSource.named.loop1, S1WalkInvalid.stop] using
    S2Loop.execute trace 1048576 (by decide)
#print axioms source_loop_total
end S1TableFault
