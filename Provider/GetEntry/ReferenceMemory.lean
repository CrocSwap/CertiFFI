import GetEntry.Full
import Walk.S1ReferenceEncoding
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 100000
namespace S1EntryReferenceMemory
open S1OuterSetup

theorem total (c : Context) (f : FaultRecord) (s : State) (n : Nat)
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false)
    (hTx : c.wp.txsz = 16#6) (hStart : c.startlevel = 0)
    (hPath : S1ResourcePath.Slots c.wp c.va s.mem n 0
      (S1EntryRoot.slot c.wp s.regs c.regime c.va))
    (observe : S1LogicalReference.Observation) (ram : FullAddress → Prop)
    (available : S1LogicalReference.Available observe ram)
    (realizes : S1LogicalReference.Realizes observe (c.wp.ee == 1#1) (c.wp.pie == 1#1)
      (c.wp.ha == 1#1) (c.wp.hd == 1#1) (fun a => s.mem[a]?)) :
    ∃ r t, AArch64_S1Walk f c.wp c.va c.regime c.acc 64 s = .ok r t ∧
      t.regs = s.regs ∧
      S1LogicalReference.Realizes observe (c.wp.ee == 1#1) (c.wp.pie == 1#1)
        (c.wp.ha == 1#1) (c.wp.hd == 1#1) (fun a => t.mem[a]?) := by
  rcases S1FullEntry.total c f s n hReady hFault hCache hTx hStart hPath with
    ⟨r, t, hr, hregs, hmem⟩
  exact ⟨r, t, hr, hregs,
    S1LogicalReference.realizes_transport observe _ _ _ _ _ _ ram available realizes
      (S1ReferenceEncoding.equivalent c.wp s.mem t.mem hmem)⟩
#print axioms total
end S1EntryReferenceMemory
