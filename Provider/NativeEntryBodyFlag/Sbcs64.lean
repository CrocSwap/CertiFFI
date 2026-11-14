import ArmCertWalk.MemFrameSbcs64
import Bridge.CruxIAdcs111
import Sail.AbstractRealRat
import NativeEntry.Effects
import NativeEntryContract.Core
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGenGuarded.BookkeepingTransport
import BookkeepingGuard.GuardedBookkeepingNonProj
import NativeEntryAdapters.PreludeInput
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyFlag.Sbcs64
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

/- Sbcs64 trio (HAND, same shape as the generated flag3 runs). Success, PhysicalCount,
mem and events from Memory's MemFrame.Sbcs64.phys (e1382e49); ActFrame, NPE and GIC
from Core's canonical SDK CruxIAdcs111 frames, transported by CruxIAdcs111.leaf_eq
(SBCS 111 = ADCS 111). HeapV2 Sbcs64 rows have Rm = XZR. -/
structure Guard (s : NativeState) (Rd Rn : BitVec 5) : Prop where
  rd : Rd.toNat < 31
  rn : Rn.toNat < 31
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2

def writes : Effects.Writes := {}

theorem run (s : NativeState) (Rd Rn : BitVec 5) (g : Guard s Rd Rn) (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 1#1 1#1 : SailM Unit) s = .ok () t ∧
      t.mem = s.mem ∧ t.events = s.events ∧ ActFrame s t ∧
      Effects.Frame writes s.regs t.regs ∧ NativeEntryContract.Frame writes s t ∧ HookQuiet ticks t := by
  have hRd : ¬ (Rd.toNat : Int) = 31 := by have := g.rd; omega
  have hRn : ¬ (Rn.toNat : Int) = 31 := by have := g.rn; omega
  have P := MemFrame.Sbcs64.phys s Rd Rn g.rd g.rn g.el g.a64 g.aa64 g.btype g.btn hRd hRn
  have ok := P.1
  have ph := congrArg Prod.fst P.2
  have pm := congrArg (fun x => x.2.1) P.2
  have pe := congrArg (fun x => x.2.2) P.2
  have L := ArmBridge.CruxIAdcs111.leaf_eq (31#5) Rn Rd
  have af := ArmBridge.CruxIAdcs111.act_frame Rat Rd Rn (31#5) s
  have npe := ArmBridge.CruxIAdcs111.act_npe Rat Rd Rn (31#5) s
  have gic := ArmBridge.CruxIAdcs111.act_gic Rat Rd Rn (31#5) s
  rw [← L] at af npe gic
  have fields : GuardFieldsEq s (resSt s ((decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn 31#5 1#1 1#1 1#1 : SailM Unit) s)) := by
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
end NativeEntryBodyFlag.Sbcs64
