import Pilot.S1WalkSource
import Pilot.S1DecodeFacts
import Walk.S1Unknowns
import Pilot.S2Loop
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1WalkInvalid
abbrev State := SequentialState Regs oracleChoiceSource
abbrev Return := FaultRecord × AddressDescriptor × TTWState × BitVec 64
abbrev Vars := Bool × FullAddress × BitVec 64 × DescriptorType × FaultRecord ×
  BitVec 64 × Bool × FaultRecord × BitVec 2 × TTWState
def stop : Vars → Bool
  | (_, _, d, _, _, newd, _, _, _, _) => newd == d
def faultResult (fault : FaultRecord) (a : AddressDescriptor) (w : TTWState)
    (d : BitVec 64) : Return := ({fault with statuscode := .Fault_Translation}, a, w, d)

theorem body_total (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (walkaddr : AddressDescriptor) (ti : TranslationInfo)
    (s2fs1mro aligned : Bool) (descaddr : FullAddress) (d : BitVec 64)
    (oldType : DescriptorType) (fault : FaultRecord) (oldNew : BitVec 64)
    (a64 : Bool) (s2fault : FaultRecord) (skl : BitVec 2) (current : TTWState)
    (s : State) (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1)
    (hTG : wp.tgx = .TGx_4KB)
    (hInvalid : S1DecodeFacts.classify d current.level = .DescriptorType_Invalid) :
    ∃ (a : AddressDescriptor) (w : TTWState) (out : BitVec 64) (t : State),
      S1WalkSource.named.body1 wp va regime acc 64 walkaddr ti s2fs1mro
        (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s =
        .ok (.error (.inr (faultResult fault a w out))) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  have hdec : AArch64_DecodeDescriptorType d 0#1 0#1 .TGx_4KB current.level =
      (pure .DescriptorType_Invalid : SailM DescriptorType) := by
    funext t
    rw [S1DecodeFacts.model_eq, hInvalid]
    rfl
  rcases S1Unknowns.address_total s with ⟨a, t1, ha, hr1, hm1, he1⟩
  rcases S1Unknowns.walkstate_total t1 with ⟨w, t2, hw, hr2, hm2, he2⟩
  rcases S1Unknowns.bits_total t2 with ⟨out, t, hout, hr3, hm3, he3⟩
  refine ⟨a, w, out, t, ?_, hr3.trans (hr2.trans hr1),
    hm3.trans (hm2.trans hm1), he3.trans (he2.trans he1)⟩
  simp only [S1WalkSource.named.body1, hD128, hDS, hTG, hdec]
  simp [faultResult, Bind.bind, Pure.pure, Functor.map, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.mk, ExceptT.lift, ExceptT.map, EStateM.bind, EStateM.map,
    EStateM.pure, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
    SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw, ha, hw, hout]

theorem source_loop_total (wp : S1TTWParams) (va : BitVec 64) (regime : Regime)
    (acc : AccessDescriptor) (walkaddr : AddressDescriptor) (ti : TranslationInfo)
    (s2fs1mro aligned : Bool) (descaddr : FullAddress) (d : BitVec 64)
    (oldType : DescriptorType) (fault : FaultRecord) (oldNew : BitVec 64)
    (a64 : Bool) (s2fault : FaultRecord) (skl : BitVec 2) (current : TTWState)
    (s : State) (hD128 : wp.d128 = 0#1) (hDS : wp.ds = 0#1)
    (hTG : wp.tgx = .TGx_4KB)
    (hInvalid : S1DecodeFacts.classify d current.level = .DescriptorType_Invalid) :
    ∃ (a : AddressDescriptor) (w : TTWState) (out : BitVec 64) (t : State),
      S1WalkSource.named.loop1 wp va regime acc 64 descaddr oldType skl current
        walkaddr ti aligned d fault a64 s2fault s2fs1mro oldNew s =
        .ok (.error (.inr (faultResult fault a w out))) t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  rcases body_total wp va regime acc walkaddr ti s2fs1mro aligned descaddr d oldType
    fault oldNew a64 s2fault skl current s hD128 hDS hTG hInvalid with
    ⟨a, w, out, t, hr, hregs, hmem, hevents⟩
  have trace : S2Loop.Trace stop
      (S1WalkSource.named.body1 wp va regime acc 64 walkaddr ti s2fs1mro)
      1 (aligned, descaddr, d, oldType, fault, oldNew, a64, s2fault, skl, current) s
      (.error (.inr (faultResult fault a w out))) t := .returned hr
  refine ⟨a, w, out, t, ?_, hregs, hmem, hevents⟩
  simpa only [S1WalkSource.named.loop1, stop] using
    S2Loop.execute trace 1048576 (by decide)
#print axioms body_total
#print axioms source_loop_total
end S1WalkInvalid
