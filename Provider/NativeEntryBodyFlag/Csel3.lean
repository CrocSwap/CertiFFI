import NativeEntryBodyFlag.Csel3Phys
import Bridge.CruxICsel3
import Sail.AbstractRealRat
import NativeEntry.Effects
import NativeEntryContract.Core
import Bridge.CruxGenGuarded.QuietTransport
import Bridge.CruxGenGuarded.BookkeepingTransport
import BookkeepingGuard.GuardedBookkeepingNonProj
import NativeEntryAdapters.PreludeInput
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace NativeEntryBodyFlag.Csel3
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGen ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

/- GENERATED flag-class trio over Core's canonical crux CruxICsel3 (Core-approved
reshape). No owned full-state root; class-fixed footprint {}. -/
structure Guard (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) : Prop where
  rd : Rd.toNat < 31
  rn : Rn.toNat < 31
  el : s.regs.PSTATE.EL = 0#2
  a64 : s.regs.PSTATE.nRW = 0#1
  aa64 : s.regs.FeatureImpl[4]! = true
  btype : s.regs.PSTATE.BTYPE = 0#2
  btn : s.regs.BTypeNext = 0#2
  spe : s.regs.bank_Bool .SPESampleInFlight = false

def writes : Effects.Writes := {}

theorem run (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (g : Guard s Rd Rn) (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1 : SailM Unit) s = .ok () t ∧ t.mem = s.mem ∧ t.events = s.events ∧ ActFrame s t ∧
      Effects.Frame writes s.regs t.regs ∧ NativeEntryContract.Frame writes s t ∧ HookQuiet ticks t := by
  have hRd : ¬ (Rd.toNat : Int) = 31 := by have := g.rd; omega
  have hRn : ¬ (Rn.toNat : Int) = 31 := by have := g.rn; omega
  have ok := (ArmBridge.CruxICsel3.madd_frame Rat (Rd) (Rn) (31#5) s ⟨g.el, g.spe⟩).1
  have af := ArmBridge.CruxICsel3.act_frame Rat (Rd) (Rn) (31#5) s
  have npe := ArmBridge.CruxICsel3.act_npe Rat (Rd) (Rn) (31#5) s
  have gic := ArmBridge.CruxICsel3.act_gic Rat (Rd) (Rn) (31#5) s
  have rg : ArmBridge.CruxICsel3.RG (Rd) (Rn) (31#5) s = ArmBridge.CruxCore.resSt s ((decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1 : SailM Unit) s) := by
    unfold ArmBridge.CruxICsel3.RG; rw [if_pos ⟨g.el, g.spe⟩]
  rw [rg] at af npe gic
  have phx := (NativeEntryBodyFlag.Csel3Phys.phys s Rd Rn g.rd g.rn g.el g.a64 g.aa64 g.btype g.btn g.spe hRd hRn).2
  have ph := congrArg Prod.fst phx
  have pm := congrArg (fun x => x.2.1) phx
  have pe := congrArg (fun x => x.2.2) phx
  have fields : GuardFieldsEq s (resSt s ((decode_csel_aarch64_instrs_integer_conditional_select Rd Rn 0#1 3#4 31#5 0#1 1#1 : SailM Unit) s)) := by
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
end NativeEntryBodyFlag.Csel3
