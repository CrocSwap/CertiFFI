import GetEntry.PathSlots
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxHeartbeats 100000
namespace S1EntryPathTotal
open S1OuterSetup S1LogicalReference

/- Full original S1Walk normality under independent logical topology + byte
   realization. VM0 only; this does not identify its returned translation with
   the independent interpreter's result, or discharge hardware setup. -/
theorem total (c : Context) (f : FaultRecord) (s : State)
    (hReady : Ready c s) (hFault : f.statuscode = .Fault_None)
    (hCache : s.regs.bank_Bool .__tlb_enabled = false)
    (hTx : c.wp.txsz = 16#6) (hStart : c.startlevel = 0)
    (observe : Observation)
    (available : Available observe (fun p => S2TableRAM.OrdinaryRAM p.address))
    (realizes : Realizes observe (c.wp.ee == 1#1) (c.wp.pie == 1#1)
      (c.wp.ha == 1#1) (c.wp.hd == 1#1) (fun a => s.mem[a]?))
    (identity : S1EntryPathSlots.Identity observe) (result : PathEnd)
    (path : Path observe (S2PhysicalSizeFrame.value c.wp.ps).toNat c.va 0 9
      ((S1EntryRoot.base c.wp s.regs c.regime c.va).setWidth 48) result) :
    ∃ r t, AArch64_S1Walk f c.wp c.va c.regime c.acc 64 s = .ok r t ∧
      t.regs = s.regs ∧
      Realizes observe (c.wp.ee == 1#1) (c.wp.pie == 1#1)
        (c.wp.ha == 1#1) (c.wp.hd == 1#1) (fun a => t.mem[a]?) := by
  have hslot := S1EntryRootGeometry.root_slot c.wp s.regs c.regime c.va c.d128 c.tg hTx
  rcases S1EntryPathSlots.of_path c.wp c.va s.mem observe available realizes identity
    path rfl (S1EntryRoot.slot c.wp s.regs c.regime c.va) hslot with ⟨n, hn⟩
  exact S1EntryReferenceMemory.total c f s n hReady hFault hCache hTx hStart hn
    observe (fun p => S2TableRAM.OrdinaryRAM p.address) available realizes
#print axioms total
end S1EntryPathTotal
