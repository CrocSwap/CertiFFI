import NativeEntryCallerTransport.Fields
import NativeEntryTail.Guard
import Bridge.CruxGenGuarded.QuietTransport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace NativeEntryCallerTransport
open ArmBridge.Boundary ArmBridge.Draft ArmBridge.CruxCore
open NativeEntryCallerParts
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open ArmBridge.CruxGenGuarded
open ArmCert.HookQuiet.V0 (HookQuiet)
open NativeEntryTail (EntryPins)

theorem bl_quiet_fields (imm26 : BitVec 26) (s : NativeState) :
    GuardFieldsEq s (blActionState imm26 s) where
  features := bl_FeatureImpl imm26 s
  el := congrArg ProcState.EL (bl_action_PSTATE imm26 s)
  nrw := congrArg ProcState.nRW (bl_action_PSTATE imm26 s)
  spe := bl_sample imm26 s
  pmuCount := congrFun (bl_bank_Int imm26 s) _
  cntcr := congrFun (bl_bank_BitVec_32 imm26 s) _
  physicalCount := bl_PhysicalCount imm26 s
  bank64 := by intro k _; exact congrFun (bl_bank_BitVec_64 imm26 s) k

theorem bl_quiet (imm26 : BitVec 26) (s : NativeState) (ticks : Nat)
    (hq : HookQuiet ticks s) : HookQuiet ticks (blActionState imm26 s) :=
  quiet_of_fields ticks s _ hq (bl_quiet_fields imm26 s)

theorem bl_pins (imm26 : BitVec 26) (s : NativeState) (hp : EntryPins s) :
    EntryPins (blActionState imm26 s) := by
  constructor
  · simpa only [bl_FeatureImpl] using hp.f4
  · simpa only [bl_FeatureImpl] using hp.rme
  · simpa only [bl_sample] using hp.spe
  · simpa only [bl_action_PSTATE] using hp.el
  · simpa only [bl_action_PSTATE] using hp.nrw
  · simpa only [bl_bank_BitVec_32] using hp.edecr
  · simpa only [bl_bank_BitVec_32] using hp.cti
  · simpa only [bl_bank_BitVec_32] using hp.st
  · simpa only [bl_bank_BitVec_32] using hp.edesr
  · rw [bl_action_type]; intro h; cases h
  · simpa only [bl___emulator_termination_opcode] using hp.emu
  · simpa only [bl_bank_BitVec_64] using hp.e2h
  · simpa only [bl_bank_BitVec_64] using hp.tge
  · simpa only [bl_bank_BitVec_64] using hp.scrns
  · simpa only [bl_bank_BitVec_64] using hp.pmbe
  · simpa only [bl_bank_BitVec_64] using hp.mdss
  · simpa only [bl_bank_BitVec_64] using hp.pmbs
  · simpa only [bl_action_PSTATE] using hp.da
  · simpa only [bl_action_PSTATE] using hp.di
  · simpa only [bl_action_PSTATE] using hp.df
  · simpa only [bl_action_PSTATE] using hp.il
  · simpa only [bl_action_PSTATE] using hp.pss

theorem blr_quiet_fields (Rn : BitVec 5) (s : NativeState) :
    GuardFieldsEq s (blrActionState Rn s) where
  features := blr_FeatureImpl Rn s
  el := congrArg ProcState.EL (blr_action_PSTATE Rn s)
  nrw := congrArg ProcState.nRW (blr_action_PSTATE Rn s)
  spe := blr_sample Rn s
  pmuCount := congrFun (blr_bank_Int Rn s) _
  cntcr := congrFun (blr_bank_BitVec_32 Rn s) _
  physicalCount := blr_PhysicalCount Rn s
  bank64 := by intro k _; exact congrFun (blr_bank_BitVec_64 Rn s) k

theorem blr_quiet (Rn : BitVec 5) (s : NativeState) (ticks : Nat)
    (hq : HookQuiet ticks s) : HookQuiet ticks (blrActionState Rn s) :=
  quiet_of_fields ticks s _ hq (blr_quiet_fields Rn s)

theorem blr_pins (Rn : BitVec 5) (s : NativeState) (hp : EntryPins s) :
    EntryPins (blrActionState Rn s) := by
  constructor
  · simpa only [blr_FeatureImpl] using hp.f4
  · simpa only [blr_FeatureImpl] using hp.rme
  · simpa only [blr_sample] using hp.spe
  · simpa only [blr_action_PSTATE] using hp.el
  · simpa only [blr_action_PSTATE] using hp.nrw
  · simpa only [blr_bank_BitVec_32] using hp.edecr
  · simpa only [blr_bank_BitVec_32] using hp.cti
  · simpa only [blr_bank_BitVec_32] using hp.st
  · simpa only [blr_bank_BitVec_32] using hp.edesr
  · rw [blr_action_type]; intro h; cases h
  · simpa only [blr___emulator_termination_opcode] using hp.emu
  · simpa only [blr_bank_BitVec_64] using hp.e2h
  · simpa only [blr_bank_BitVec_64] using hp.tge
  · simpa only [blr_bank_BitVec_64] using hp.scrns
  · simpa only [blr_bank_BitVec_64] using hp.pmbe
  · simpa only [blr_bank_BitVec_64] using hp.mdss
  · simpa only [blr_bank_BitVec_64] using hp.pmbs
  · simpa only [blr_action_PSTATE] using hp.da
  · simpa only [blr_action_PSTATE] using hp.di
  · simpa only [blr_action_PSTATE] using hp.df
  · simpa only [blr_action_PSTATE] using hp.il
  · simpa only [blr_action_PSTATE] using hp.pss

#print axioms bl_quiet_fields
#print axioms bl_quiet
#print axioms bl_pins
#print axioms blr_quiet_fields
#print axioms blr_quiet
#print axioms blr_pins
end NativeEntryCallerTransport
