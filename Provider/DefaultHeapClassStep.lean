-- The actual scalar successor, its value effect, and the event record.
import DefaultHeapEntryMem
import DefaultScalarTrace
import DefaultHeapClassEntry
import HeapV2StepCerts.TailWF
import HeapV2StepCerts.TailWN

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk ArmBridge.Draft ArmBridge.Boundary
open ArmBridge.CruxGenGuarded ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV3
open ArmBridge.CruxCore ArmBridge.CruxGenGuarded.EntryClassNext
open ArmCert.HookQuiet.V0 (HookQuiet)
open HeapV2StepCerts

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

namespace ReleaseProfile.DefaultHeapClassStep
open DefaultHeapEntryMem

theorem fromWF {real : Type} [Sail.SailReal real] {w : BitVec 32}
    {writes : NativeEntry.Effects.Writes} {K : Int} {x : NativeState} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)} {k : Nat}
    (tail : TailWE.ClassTailWFAt real w writes K x next us k) :
    TailWE.ClassTailWAt real w writes K x next us k := by
  intro fetched enc budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, run, frame, q, pin, sys, mem, gic, pc, np, ev, z, hold, value, _⟩ :=
    tail fetched enc budget pins input guard quiet it ss
  exact ⟨sp, a, fin, hook, run, frame, q, pin, sys, mem, gic, pc, np, ev, z, hold, value⟩

theorem fromWN {real : Type} [Sail.SailReal real] {w : BitVec 32}
    {writes : NativeEntry.Effects.Writes} {K : Int} {x : NativeState} {next : BitVec 64}
    {us : List (RegBind.Reg × RegBind.Upd)} {k : Nat}
    (tail : TailWE.ClassTailWNAt real w writes K x next us k) :
    TailWE.ClassTailWAt real w writes K x next us k := by
  intro fetched enc budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, run, frame, q, pin, sys, mem, gic, pc, np, ev, z, hold, value, _⟩ :=
    tail fetched enc budget pins input guard quiet it ss
  exact ⟨sp, a, fin, hook, run, frame, q, pin, sys, mem, gic, pc, np, ev, z, hold, value⟩

structure Effects {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (mapping : BitVec 64 → Option Nat) (k : Nat) (x fin : NativeState) : Prop where
  holds : RegBind.Holds (RegBind.upds k) x fin
  value : ValBind.VEff k x fin
  mem : fin.mem = x.mem
  gcs : fin.regs.bank_BitVec_64 .SCR_EL3 = x.regs.bank_BitVec_64 .SCR_EL3
  z : fin.regs._Z = x.regs._Z
  events : StepEvents.EvShape spec mapping [] x fin

#check "CURRENT_DECL HeapClassStep.step"
theorem step (real : Type) [Sail.SailReal real]
    {domain : QueryDomain} (spec : TopologyImageSpec domain)
    (config : AttributeConfig) (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap)
    (scope : Nat → Prop) (image : MemReloc.Image) (loadBase : MemReloc.Word)
    (separated : ImageTableSeparated scope loadBase mapping (rowsFootprint spec.imageRows).byte)
    (base : BitVec 64) (offset : Nat → BitVec 64) (budget : Nat) (p : HeapV2E17.Pins) (k : Nat)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (capacity : Nat) (drawsBefore : Nat → Nat)
    (drawsNext : drawsBefore k ≤ drawsBefore (k + 1))
    (room : k < budget) (hk : k < 358) (page : base.toNat % 4096 = 0)
    (aligned : (offset k).toNat % 4 = 0)
    (w : BitVec 32) (writes : NativeEntry.Effects.Writes) (K : Int)
    (x : NativeState) (inv : HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue entry capacity drawsBefore k x)
    (tail : TailWE.ClassTailWAt real w writes K x (x.regs._PC + 4#64) (RegBind.upds k) k)
    (tailChoice : DefaultScalarTrace.TailChoiceAt real x w)
    (target : x.regs._PC + 4#64 = base + offset (k + 1))
    (nodup : (spec.logicalRows.map (·.logical)).Nodup)
    (ob : FetchObligations spec config rows mapping w x) :
    ∃ fin, modelStep real x = .ok () fin ∧
      HeapInv spec config rows mapping m scope image loadBase base offset budget p catalogue entry capacity drawsBefore (k + 1) fin ∧
      Effects spec mapping k x fin := by
  have core := inv.core
  have hq : HookQuiet ((budget - (k + 1)) + 1) x := by
    have e : budget - (k + 1) + 1 = budget - k := by omega
    rw [e]; exact core.v1.quiet
  obtain ⟨fin, run, pins, quiet, current, pc, debug, features, gic, closed, placed,
      bp, holds, mem, sys, value, gcs, z, tco, events, control⟩ :=
    DefaultHeapClassEntry.entry_class_next_z real spec config rows mapping w writes K x core.v1.pins
      (x.regs._PC + 4#64) (offset (k + 1)) (RegBind.upds k) k tail
      core.v1.gic core.v1.features core.v1.debug (budget - (k + 1)) hq base (offset k) core.v1.pc
      page aligned target core.v1.current m core.closed scope image loadBase core.placed separated
      core.branch core.raw core.noUpd ob.queryOf ob.rawOf ob.vaOf ob.mmio ob.present ob.perAcc nodup ob.code
  have choice := DefaultScalarTrace.step_choice real spec config rows mapping m scope image loadBase
    base offset budget catalogue k room page aligned w x fin core ob tailChoice run
  obtain ⟨used, prefixChoice, prefixBound⟩ := inv.trace
  refine ⟨fin, run, ⟨⟨⟨pins, features, debug, current, quiet, gic, pc⟩, closed, placed, bp, ?_, ?_,
    postFrame sys core.post, MemConfigFrame.mode sys.feat sys.el sys.scr sys.hcr core.mode,
    MemConfigFrame.debug sys.mdscr sys.hde core.debug, ?_,
    MemConfigFrame.dcache sys.sctlr core.dcache,
    DefaultActionControls.controls_of_sys core.controls sys tco⟩,
    RegBind.carry_step hk holds inv.regBind, ?_, inv.statusRows,
    ⟨used, by simpa only [Nat.add_zero] using NativeMteTagCheck.choice_delta_trans prefixChoice choice,
      by omega⟩, inv.control.trans control⟩, ⟨holds, value, mem, gcs, z, events⟩⟩
  · rw [mem]; exact core.raw
  · intro wr acc hs; rw [hostHAFT_eq sys]; exact core.noUpd wr acc hs
  · rw [sys.feat]; exact core.feat
  · intro e he n hn i hi; rw [mem]; exact inv.present e he n hn i hi

#print axioms step
end ReleaseProfile.DefaultHeapClassStep
