import DefaultHeapEntryMem
import TranslateStepV.BlNZ
-- the heap-v2 BL step facts (k = 15, 150, 252) for stepV_k. CallerBl.native_tail_ez
-- (RtB6.BlTailZ) re-run with the NZCV carry added (NativeEntryCallerParts.bl_action_PSTATE + the PMU E20 frame), as
-- BlTailNZ; entry_bl_next_X = RtB3.RichH.entry_class_next_v3_blL reduced to the value frame; bl_vholds concludes
-- VHolds [(.x 30, none)] none (X30 clobbered, every other GPR, SP and NZCV kept) and memory kept.
import Bridge.CruxGenGuarded.EntryBl
import Bridge.CruxGenGuarded.ClosedChain
import RtB3.RichH
import TranslateStepV.BranchX
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmCert.Translate ArmCert.Translate.Model
open ArmCertWalk
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen
open ArmBridge.CruxGenGuarded.EntryActualFetch ArmBridge.CruxGenGuarded.EntryFetchedFacts
open ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeEntryTail (EntryPins)

namespace ReleaseProfile.DefaultHeapValueBl
open TranslateStepV.BlNZ NativeEntryCallerParts
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
theorem bl_vholds (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (room : k < budget) (page : base.toNat % 4096 = 0) (aligned : (offset k).toNat % 4 = 0)
    (imm26 : BitVec 26)
    (x : NativeState) (inv : DefaultHeapEntryMem.HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue entry capacity drawsBefore k x)
    (controls : CallerControls x) (tail : BlTailNZ real imm26 x)
    (obligations : ∀ x, DefaultHeapEntryMem.HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue entry capacity drawsBefore k x →
      FetchObligations spec config rows mapping (NativeEntryCallerDispatch.Bl.word imm26) x) :
    ∃ fin, modelStep real x = .ok () fin ∧ ArmCertValue.VHolds [(.x 30, none)] none x fin ∧ fin.mem = x.mem := by
  have ob := obligations x inv
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact inv.core.v1.quiet
  obtain ⟨fin, run, g, sp, n, z, c, v, mem⟩ :=
    entry_bl_next_X real spec config rows mapping imm26 x inv.core.v1.pins tail controls inv.core.v1.gic
      inv.core.v1.features inv.core.v1.debug (budget - (k + 1)) hq base (offset k) inv.core.v1.pc page aligned
      inv.core.v1.current m inv.core.closed scope image loadBase inv.core.placed separated
      inv.core.raw inv.core.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc ob.code
  exact ⟨fin, run, vholds_bl _ g sp n z c v, mem⟩


#print axioms bl_vholds
end ReleaseProfile.DefaultHeapValueBl
