import GetEntry.Root
import GetEntry.WP
import Walk.S1WalkTail
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 150000
namespace S1EntryTail
open S1OuterSetup
abbrev Return := S1WalkTail.Return

def Post (c : Context) (s : State) (_r : Return) (t : State) : Prop :=
  t.regs = s.regs ∧
    S1MemoryObservation.Equivalent (S1TableUpdate10.observe c.wp) s.mem t.mem

theorem total (c : Context) (ctx : TLBContext) (entry : TLBRecord)
    (aligned : Bool) (descaddr : FullAddress) (d : BitVec 64)
    (typ : DescriptorType) (f : FaultRecord) (a64 mro : Bool) (skl : BitVec 2)
    (walkaddr : AddressDescriptor) (w : TTWState) (s : State) (n : Nat)
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hPAS : w.baseaddress.paspace = .PAS_NonSecure)
    (hPath : S1ResourcePath.Slots c.wp c.va s.mem n w.level descaddr)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false) :
    S1EntryWP.WP
      (S1WalkTailSource.tail c.wp c.va c.regime c.acc 64 a64 aligned f ctx entry w c.startlevel
        d skl walkaddr mro typ descaddr) s (Post c s) (Post c s) := by
  rcases S1WalkTail.total c ctx entry aligned descaddr d typ f a64 mro skl walkaddr w s n
    hReady hFault hPAS hPath hCache with ⟨steps, r, t, hp, hb, hr, hregs, hmem⟩
  exact S1EntryWP.of_run _ s t r (Post c s) hr ⟨hregs, hmem⟩
#print axioms total
end S1EntryTail
