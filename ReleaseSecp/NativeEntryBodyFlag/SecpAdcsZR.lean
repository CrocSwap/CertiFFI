import NativeEntryBodyFlag.SecpAdcsZRPhys
import Bridge.CruxIAdcs101
import Sail.AbstractRealRat
import NativeEntry.Effects
import NativeEntryContract.Core
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGenGuarded.BookkeepingTransport
import BookkeepingGuard.GuardedBookkeepingNonProj
import NativeEntryAdapters.PreludeInput
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyFlag.SecpAdcsZR
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

/- GENERATED flag-class trio over Core's canonical crux CruxIAdcs101 (Core-approved
reshape). No owned full-state root; class-fixed footprint {}. -/
structure Guard (s : NativeState) (Rn : BitVec 5) : Prop where
  rn : Rn.toNat < 31
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2

def writes : Effects.Writes := {}

theorem run (s : NativeState) (Rn : BitVec 5) (g : Guard s Rn) (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry 31#5 Rn 31#5 1#1 0#1 1#1 : SailM Unit) s = .ok () t ∧ t.mem = s.mem ∧ t.events = s.events ∧ ActFrame s t ∧
      Effects.Frame writes s.regs t.regs ∧ NativeEntryContract.Frame writes s t ∧ HookQuiet ticks t := by
  have hRn : ¬ (Rn.toNat : Int) = 31 := by have := g.rn; omega
  have ok := (ArmBridge.CruxIAdcs101.madd_frame Rat (31#5) (Rn) (31#5) s).1
  have af := ArmBridge.CruxIAdcs101.act_frame Rat (31#5) (Rn) (31#5) s
  have npe := ArmBridge.CruxIAdcs101.act_npe Rat (31#5) (Rn) (31#5) s
  have gic := ArmBridge.CruxIAdcs101.act_gic Rat (31#5) (Rn) (31#5) s
  have phx := (NativeEntryBodyFlag.SecpAdcsZRPhys.phys s Rn g.rn g.el g.a64 g.aa64 g.btype g.btn hRn).2
  have ph := congrArg Prod.fst phx
  have pm := congrArg (fun x => x.2.1) phx
  have pe := congrArg (fun x => x.2.2) phx
  have fields : GuardFieldsEq s (resSt s ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry 31#5 Rn 31#5 1#1 0#1 1#1 : SailM Unit) s)) := by
    constructor
    · exact af.feat
    · simpa using congrArg ProcState.EL af.pse
    · simpa using congrArg ProcState.nRW af.pse
    · exact congrFun af.bbool _
    · exact congrFun af.bint _
    · exact congrFun af.b32 _
    · exact ph
    · intro k _; exact congrFun af.b64 k
  exact ⟨_, ok, pm, pe, af, Effects.of_scalar writes npe, NativeEntryContract.of_scalar af npe gic,
    quiet_of_fields ticks s _ hq fields⟩

#print axioms run
end NativeEntryBodyFlag.SecpAdcsZR
