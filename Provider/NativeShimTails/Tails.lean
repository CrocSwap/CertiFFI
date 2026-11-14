import Bridge.CruxGenGuarded.EntryClassNext
import HeapV2StepCerts.RegVal
import HeapV2StepCerts.BodyHolds
import HeapV2StepCerts.MemHolds
import HeapV2StepCerts.ActionTransport

/-! Core f83f (1): decision-179 shim tails in `HeapV2StepCerts.RegVal.ClassTailVAt` form (next = PC+4),
from Core's `ArmBridge.CruxGenGuarded.Entry<K>.native_tail`, plus the DIT effect lemmas at the tail's
final state. ISB SY / DIT on / DIT off / MSR DIT, Xt: us = []. MRS Xt, DIT: us = [(.x Xt, .drop)].
BTI c stays with Core's EntryBtiNext. HAND. -/

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
namespace NativeShimTails
open HeapV2StepCerts

/-- BTI c (the shim s0, word 0xd503245f): no Profile premise; Core native_tail takes EntryPins, obtained from StepPins. -/
theorem btiC_tailVAt (real : Type) [Sail.SailReal real] (source : NativeState) :
    RegVal.ClassTailVAt real NativeEntryDispatch.BtiC.word NativeEntryAdapters.BtiC.writes 97 source
      (source.regs._PC + 4#64) [] := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, proj, frame, q, p, sys, _, output, mem, _, gic, _, pc, np⟩ :=
    EntryBtiC.native_tail real source fetched enc0 (NativeEntryTail.EntryPins.of_scalar fetched pins) input guard
      budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have ra := congrArg Prod.fst proj
  change a.regs = _ at ra
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ?_⟩
  exact RegBind.Holds.of_prefix (ActionTransport.gpr post.frame) (ActionTransport.sp0 post.frame)
    (RegBind.holds_nil (actionState NativeEntryDispatch.BtiC.word sp 97) fin (by rw [output.gpr, ra]; rfl) (by rw [output.sp, ra]; rfl))

/-- BTI c landing facts: the run succeeds, the final state is StepPins (BTYPE = 0, BTypeNext = 0 for the
    next step), DIT is unchanged, and memory/events are the fetched ones. -/
theorem btiC_fin (real : Type) [Sail.SailReal real] (source fetched : NativeState) (enc0 : __InstrEnc)
    (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched) (budget : Nat)
    (quiet : HookQuiet (budget + 1) fetched) (it : fetched.regs.ShouldAdvanceIT = false)
    (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeTail real source NativeEntryDispatch.BtiC.word enc0 fetched = .ok () fin ∧
      StepPins fin ∧ fin.regs.PSTATE.BTYPE = 0#2 ∧ fin.regs.BTypeNext = 0#2 ∧
      fin.regs.PSTATE.DIT = fetched.regs.PSTATE.DIT ∧ fin.mem = fetched.mem ∧ fin.events = fetched.events ∧
      fin.regs._PC = source.regs._PC + 4#64 := by
  obtain ⟨sp, a, fin, hook, _, tail, proj, _, _, p, _, _, _, mem, ev, _, dit, pc, _⟩ :=
    EntryBtiC.native_tail real source fetched enc0 (NativeEntryTail.EntryPins.of_scalar fetched pins) input guard
      budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have ra := congrArg Prod.fst proj
  change a.regs = _ at ra
  refine ⟨fin, tail, p, p.btype, p.btn, ?_, mem, ev, pc⟩
  rw [dit, ra]
  exact congrArg (fun q => q.DIT) (ActionTransport.pstate (w := NativeEntryDispatch.BtiC.word) (K := 97) post.frame)

theorem isbSy_tailVAt (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.IsbSy.Profile source) :
    RegVal.ClassTailVAt real NativeEntryDispatch.IsbSy.word NativeEntryAdapters.IsbSy.writes 483 source
      (source.regs._PC + 4#64) [] := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, proj, frame, q, p, sys, _, output, mem, _, gic, _, pc, np⟩ :=
    EntryIsbSy.native_tail real source fetched enc0 profile pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have ra := congrArg Prod.fst proj
  change a.regs = _ at ra
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ?_⟩
  exact RegBind.Holds.of_prefix (ActionTransport.gpr post.frame) (ActionTransport.sp0 post.frame)
    (RegBind.holds_nil (actionState NativeEntryDispatch.IsbSy.word sp 483) fin (by rw [output.gpr, ra]; rfl) (by rw [output.sp, ra]; rfl))

theorem ditOn_tailVAt (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.DitOn.Profile source) :
    RegVal.ClassTailVAt real NativeEntryDispatch.DitOn.word NativeEntryAdapters.DitOn.writes 703 source
      (source.regs._PC + 4#64) [] := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, proj, frame, q, p, sys, _, output, mem, _, gic, _, pc, np⟩ :=
    EntryDitOn.native_tail real source fetched enc0 profile pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have ra := congrArg Prod.fst proj
  change a.regs = _ at ra
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ?_⟩
  exact RegBind.Holds.of_prefix (ActionTransport.gpr post.frame) (ActionTransport.sp0 post.frame)
    (RegBind.holds_nil (actionState NativeEntryDispatch.DitOn.word sp 703) fin (by rw [output.gpr, ra]; rfl) (by rw [output.sp, ra]; rfl))

theorem ditOff_tailVAt (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.DitOff.Profile source) :
    RegVal.ClassTailVAt real NativeEntryDispatch.DitOff.word NativeEntryAdapters.DitOff.writes 703 source
      (source.regs._PC + 4#64) [] := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, proj, frame, q, p, sys, _, output, mem, _, gic, _, pc, np⟩ :=
    EntryDitOff.native_tail real source fetched enc0 profile pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have ra := congrArg Prod.fst proj
  change a.regs = _ at ra
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ?_⟩
  exact RegBind.Holds.of_prefix (ActionTransport.gpr post.frame) (ActionTransport.sp0 post.frame)
    (RegBind.holds_nil (actionState NativeEntryDispatch.DitOff.word sp 703) fin (by rw [output.gpr, ra]; rfl) (by rw [output.sp, ra]; rfl))

theorem msrDit_tailVAt (real : Type) [Sail.SailReal real] (source : NativeState) (Rt : BitVec 5) (rt : Rt.toNat < 31)
    (profile : NativeEntryAdapters.MsrDit.Profile source) :
    RegVal.ClassTailVAt real (NativeEntryDispatch.MsrDit.word Rt) NativeEntryAdapters.MsrDit.writes 702 source
      (source.regs._PC + 4#64) [] := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, proj, frame, q, p, sys, _, output, mem, _, gic, _, pc, np⟩ :=
    EntryMsrDit.native_tail real source fetched enc0 Rt rt profile pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have ra := congrArg Prod.fst proj
  change a.regs = _ at ra
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ?_⟩
  exact RegBind.Holds.of_prefix (ActionTransport.gpr post.frame) (ActionTransport.sp0 post.frame)
    (RegBind.holds_nil (actionState (NativeEntryDispatch.MsrDit.word Rt) sp 702) fin (by rw [output.gpr, ra]; rfl) (by rw [output.sp, ra]; rfl))

theorem mrsDit_tailVAt (real : Type) [Sail.SailReal real] (source : NativeState) (Rt : BitVec 5) (rt : Rt.toNat < 31)
    (profile : NativeEntryAdapters.MrsDit.Profile source) :
    RegVal.ClassTailVAt real (NativeEntryDispatch.MrsDit.word Rt) NativeEntryAdapters.MrsDit.writes 701 source
      (source.regs._PC + 4#64) [(.x (GPRSummary.key Rt.toNat), .drop)] := by
  intro fetched enc0 budget pins input guard quiet it ss
  obtain ⟨sp, a, fin, hook, _, tail, proj, frame, q, p, sys, _, output, mem, _, gic, _, pc, np⟩ :=
    EntryMrsDit.native_tail real source fetched enc0 Rt rt profile pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have ra := congrArg Prod.fst proj
  change a.regs = _ at ra
  refine ⟨sp, a, fin, hook, tail, frame, q, p, sys, mem, gic, pc, np, ?_⟩
  exact RegBind.Holds.of_prefix (ActionTransport.gpr post.frame) (ActionTransport.sp0 post.frame)
    (RegBind.holds_drop1 (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701) fin _ _ (by rw [output.gpr, ra]; rfl) (by rw [output.sp, ra]; rfl))

/-- The shim's MRS X9, DIT: us = [(.x 9, .drop)]. -/
theorem mrsDit9_tailVAt (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.MrsDit.Profile source) :
    RegVal.ClassTailVAt real (NativeEntryDispatch.MrsDit.word 9#5) NativeEntryAdapters.MrsDit.writes 701 source
      (source.regs._PC + 4#64) [(.x 9, .drop)] :=
  RegVal.ClassTailVAt.holds (by decide) (mrsDit_tailVAt real source 9#5 (by decide) profile)

/-- The shim's MSR DIT, X9. -/
theorem msrDit9_tailVAt (real : Type) [Sail.SailReal real] (source : NativeState)
    (profile : NativeEntryAdapters.MsrDit.Profile source) :
    RegVal.ClassTailVAt real (NativeEntryDispatch.MsrDit.word 9#5) NativeEntryAdapters.MsrDit.writes 702 source
      (source.regs._PC + 4#64) [] :=
  msrDit_tailVAt real source 9#5 (by decide) profile

/-! DIT effects at the tail's final state. `nativeTail` is a function, so the `fin` below is THE
final state of any run with these premises. -/

theorem ditOn_dit (real : Type) [Sail.SailReal real] (source fetched : NativeState) (enc0 : __InstrEnc)
    (profile : NativeEntryAdapters.DitOn.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched) (budget : Nat)
    (quiet : HookQuiet (budget + 1) fetched) (it : fetched.regs.ShouldAdvanceIT = false)
    (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeTail real source NativeEntryDispatch.DitOn.word enc0 fetched = .ok () fin ∧
      fin.regs.PSTATE.DIT = 1#1 := by
  obtain ⟨sp, a, fin, hook, _, tail, proj, _, _, _, _, _, _, _, _, _, dit, _⟩ :=
    EntryDitOn.native_tail real source fetched enc0 profile pins input guard budget quiet it ss
  have ra := congrArg Prod.fst proj
  change a.regs = _ at ra
  exact ⟨fin, tail, by rw [dit, ra]; rfl⟩

theorem ditOff_dit (real : Type) [Sail.SailReal real] (source fetched : NativeState) (enc0 : __InstrEnc)
    (profile : NativeEntryAdapters.DitOff.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched) (budget : Nat)
    (quiet : HookQuiet (budget + 1) fetched) (it : fetched.regs.ShouldAdvanceIT = false)
    (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeTail real source NativeEntryDispatch.DitOff.word enc0 fetched = .ok () fin ∧
      fin.regs.PSTATE.DIT = 0#1 := by
  obtain ⟨sp, a, fin, hook, _, tail, proj, _, _, _, _, _, _, _, _, _, dit, _⟩ :=
    EntryDitOff.native_tail real source fetched enc0 profile pins input guard budget quiet it ss
  have ra := congrArg Prod.fst proj
  change a.regs = _ at ra
  exact ⟨fin, tail, by rw [dit, ra]; rfl⟩

theorem isbSy_dit (real : Type) [Sail.SailReal real] (source fetched : NativeState) (enc0 : __InstrEnc)
    (profile : NativeEntryAdapters.IsbSy.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched) (budget : Nat)
    (quiet : HookQuiet (budget + 1) fetched) (it : fetched.regs.ShouldAdvanceIT = false)
    (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeTail real source NativeEntryDispatch.IsbSy.word enc0 fetched = .ok () fin ∧
      fin.regs.PSTATE.DIT = fetched.regs.PSTATE.DIT := by
  obtain ⟨sp, a, fin, hook, _, tail, proj, _, _, _, _, _, _, _, _, _, dit, _⟩ :=
    EntryIsbSy.native_tail real source fetched enc0 profile pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have ra := congrArg Prod.fst proj
  change a.regs = _ at ra
  refine ⟨fin, tail, ?_⟩
  rw [dit, ra]
  exact congrArg (fun p => p.DIT) (ActionTransport.pstate post.frame)

/-- MSR DIT, Xt: the final DIT is bit 24 of the FETCHED-state Xt. -/
theorem msrDit_dit (real : Type) [Sail.SailReal real] (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rt : BitVec 5) (rt : Rt.toNat < 31)
    (profile : NativeEntryAdapters.MsrDit.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched) (budget : Nat)
    (quiet : HookQuiet (budget + 1) fetched) (it : fetched.regs.ShouldAdvanceIT = false)
    (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeTail real source (NativeEntryDispatch.MsrDit.word Rt) enc0 fetched = .ok () fin ∧
      fin.regs.PSTATE.DIT = BitVec.setWidth 1
        (BitVec.join1 [BitVec.access fetched.regs.gpr[(GPRSummary.key Rt.toNat).val] 24]) := by
  obtain ⟨sp, a, fin, hook, _, tail, proj, _, _, _, _, _, _, _, _, _, dit, _⟩ :=
    EntryMsrDit.native_tail real source fetched enc0 Rt rt profile pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have ra := congrArg Prod.fst proj
  change a.regs = _ at ra
  refine ⟨fin, tail, ?_⟩
  rw [dit, ra]
  change BitVec.setWidth 1 (BitVec.join1 [BitVec.access (actionState _ sp 702).regs.gpr[(GPRSummary.key Rt.toNat).val] 24]) = _
  rw [ActionTransport.gpr post.frame]

/-- MRS Xt, DIT: the final Xt holds the FETCHED-state DIT at bit 24 (zeros elsewhere), and DIT is unchanged. -/
theorem mrsDit_dit (real : Type) [Sail.SailReal real] (source fetched : NativeState) (enc0 : __InstrEnc)
    (Rt : BitVec 5) (rt : Rt.toNat < 31)
    (profile : NativeEntryAdapters.MrsDit.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched) (budget : Nat)
    (quiet : HookQuiet (budget + 1) fetched) (it : fetched.regs.ShouldAdvanceIT = false)
    (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeTail real source (NativeEntryDispatch.MrsDit.word Rt) enc0 fetched = .ok () fin ∧
      fin.regs.gpr[(GPRSummary.key Rt.toNat).val] = (0#39 +++ fetched.regs.PSTATE.DIT) +++ 0#24 ∧
      fin.regs.PSTATE.DIT = fetched.regs.PSTATE.DIT := by
  obtain ⟨sp, a, fin, hook, _, tail, proj, _, _, _, _, _, output, _, _, _, dit, _⟩ :=
    EntryMrsDit.native_tail real source fetched enc0 Rt rt profile pins input guard budget quiet it ss
  have post := entry_spec_post fetched sp (budget + 1) quiet hook
  have ra := congrArg Prod.fst proj
  change a.regs = _ at ra
  have ps : (actionState (NativeEntryDispatch.MrsDit.word Rt) sp 701).regs.PSTATE = fetched.regs.PSTATE :=
    ActionTransport.pstate post.frame
  refine ⟨fin, tail, ?_, ?_⟩
  · rw [output.gpr, ra]
    simp only [NativeEntry.MrsDit.expected, Vector.getElem_set_self]
    rw [ps]
  · rw [dit, ra]
    exact congrArg (fun p => p.DIT) ps

/-- Same at the shim's register X9. -/
theorem mrsDit9_dit (real : Type) [Sail.SailReal real] (source fetched : NativeState) (enc0 : __InstrEnc)
    (profile : NativeEntryAdapters.MrsDit.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched) (budget : Nat)
    (quiet : HookQuiet (budget + 1) fetched) (it : fetched.regs.ShouldAdvanceIT = false)
    (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeTail real source (NativeEntryDispatch.MrsDit.word 9#5) enc0 fetched = .ok () fin ∧
      fin.regs.gpr[9] = (0#39 +++ fetched.regs.PSTATE.DIT) +++ 0#24 ∧
      fin.regs.PSTATE.DIT = fetched.regs.PSTATE.DIT :=
  mrsDit_dit real source fetched enc0 9#5 (by decide) profile pins input guard budget quiet it ss

/-- The Sail bit-24 read as extractLsb. -/
theorem bit24 (x : BitVec 64) :
    BitVec.setWidth 1 (BitVec.join1 [BitVec.access x 24]) = x.extractLsb 24 24 := by
  simp only [BitVec.access]
  generalize hb : x[24]! = b
  have r : x.extractLsb 24 24 = BitVec.ofBool b := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have e : i = 0 := by omega
    subst e
    rw [← hb]
    simp
  rw [r]
  cases b <;> decide

theorem msrDit9_dit (real : Type) [Sail.SailReal real] (source fetched : NativeState) (enc0 : __InstrEnc)
    (profile : NativeEntryAdapters.MsrDit.Profile source) (pins : StepPins fetched)
    (input : NativeEntryInput.Input source fetched) (guard : MetadataGuard fetched) (budget : Nat)
    (quiet : HookQuiet (budget + 1) fetched) (it : fetched.regs.ShouldAdvanceIT = false)
    (ss : fetched.regs.ShouldAdvanceSS = true) :
    ∃ fin, nativeTail real source (NativeEntryDispatch.MsrDit.word 9#5) enc0 fetched = .ok () fin ∧
      fin.regs.PSTATE.DIT = fetched.regs.gpr[9].extractLsb 24 24 := by
  obtain ⟨fin, tail, d⟩ := msrDit_dit real source fetched enc0 9#5 (by decide) profile pins input guard budget quiet it ss
  exact ⟨fin, tail, d.trans (bit24 _)⟩

#print axioms btiC_tailVAt
#print axioms btiC_fin
#print axioms isbSy_tailVAt
#print axioms ditOn_tailVAt
#print axioms ditOff_tailVAt
#print axioms msrDit_tailVAt
#print axioms mrsDit_tailVAt
#print axioms mrsDit9_tailVAt
#print axioms msrDit9_tailVAt
#print axioms ditOn_dit
#print axioms ditOff_dit
#print axioms isbSy_dit
#print axioms msrDit_dit
#print axioms mrsDit_dit
#print axioms mrsDit9_dit
#print axioms bit24
#print axioms msrDit9_dit
end NativeShimTails
