import Bridge.CruxGenGuarded.EntryTail
import Bridge.CruxGenGuarded.OwnerCounterSpec
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.CruxGenGuarded
open ArmBridge.Draft ArmBridge.CruxCore
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 512
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000

/- The existing metadata constructor leaves these controls unchanged. -/
theorem entryPins_at_metadata (s : NativeState) (w : BitVec 32) (K : Int)
    (hp : NativeEntryTail.EntryPins s) : NativeEntryTail.EntryPins (actionState w s K) := by
  constructor
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.f4
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.rme
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.spe
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.el
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.nrw
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.edecr
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.cti
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.st
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.edesr
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.btt
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.emu
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.e2h
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.tge
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.scrns
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.pmbe
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.mdss
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.pmbs
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.da
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.di
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.df
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.il
  · simpa (disch := decide) only [actionState, RegMap.set_ne] using hp.pss

/- Derive the fixed producer's frame for the SAME deterministic hook result.
No frame/success callback or alternate execution state is assumed. -/
theorem entry_spec_post (s sp : NativeState) (ticks : Nat) (quiet : HookQuiet ticks s)
    (hook : (PMUEvent PMU_EVENT_INST_SPEC : SailM Unit) s = .ok () sp) :
    HookPost E20Frame ticks s sp := by
  obtain ⟨actual, run, post⟩ := Owner.spec_rule ticks s quiet
  have same : sp = actual := by injection hook.symm.trans run
  subst actual
  exact post

#print axioms entryPins_at_metadata
#print axioms entry_spec_post
end ArmBridge.CruxGenGuarded
