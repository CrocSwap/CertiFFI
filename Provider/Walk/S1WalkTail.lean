import Walk.S1OuterFinite
import Walk.S1WalkSuffix
import Walk.S1WalkTailSource
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 200000
set_option maxRecDepth 1000000
namespace S1WalkTail
open S1OuterSetup
abbrev Return := S1WalkSuffix.Return

/- Exactly the original outer loop followed by the continuation extracted from
   the complete generated S1Walk; prefix initialization is composed separately. -/
noncomputable def action (c : Context) (ctx : TLBContext) (entry : TLBRecord)
    (aligned : Bool) (descaddr : FullAddress) (d : BitVec 64)
    (typ : DescriptorType) (f : FaultRecord) (a64 mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (w : TTWState) : SailM Return := SailME.run
  (S1WalkTailSource.tail c.wp c.va c.regime c.acc 64 a64 aligned f ctx entry w c.startlevel
    d skl walkaddr mro typ descaddr)

theorem total (c : Context) (ctx : TLBContext) (entry : TLBRecord)
    (aligned : Bool) (descaddr : FullAddress) (d : BitVec 64)
    (typ : DescriptorType) (f : FaultRecord) (a64 mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (w : TTWState) (s : State) (n : Nat)
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hPAS : w.baseaddress.paspace = .PAS_NonSecure)
    (hPath : S1ResourcePath.Slots c.wp c.va s.mem n w.level descaddr)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false) :
    ∃ (steps : Nat) (r : Return) (t : State),
      0 < steps ∧ steps ≤ (4 - w.level).toNat ∧
      action c ctx entry aligned descaddr d typ f a64 mro skl walkaddr w s = .ok r t ∧
      t.regs = s.regs ∧
      S1MemoryObservation.Equivalent (S1TableUpdate10.observe c.wp) s.mem t.mem := by
  rcases S1OuterFinite.loop_total c aligned descaddr d typ f a64 mro skl walkaddr w s n
    hReady hFault hPAS hPath with ⟨steps, result, t, hpos, hbound, hloop, hend, hr, hm⟩
  cases result with
  | error e =>
    cases e with
    | inl err => exact False.elim hend
    | inr r =>
      refine ⟨steps, r, t, hpos, hbound, ?_, hr, hm⟩
      simp [action, S1WalkTailSource.tail, SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run,
        ExceptT.bindCont, EStateM.bind, Pure.pure, EStateM.pure, hloop]
  | ok vars =>
    rcases vars with ⟨aligned', slot', d', typ', f', a64', mro', skl', walkaddr', w'⟩
    rcases hend with ⟨hstop, hlevels⟩
    have hs : S1WalkSuffix.Safe t.regs :=
      ⟨by rw [hr]; exact hReady.pa, by rw [hr]; exact hCache⟩
    rcases S1WalkSuffix.normal c.wp c.va c.regime c.acc ctx entry aligned' slot' d' typ' f'
      a64' mro' skl' walkaddr' w' c.d128 c.tg hlevels t hs with
      ⟨r, u, hsuffix, ⟨hr2, hm2, _⟩, _⟩
    refine ⟨steps, r, u, hpos, hbound, ?_, hr2.trans hr, ?_⟩
    · simp [action, S1WalkTailSource.tail, SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run,
        ExceptT.bindCont, EStateM.bind, Pure.pure, EStateM.pure, hloop, hsuffix]
    · simpa only [hm2] using hm
#print axioms total
end S1WalkTail
