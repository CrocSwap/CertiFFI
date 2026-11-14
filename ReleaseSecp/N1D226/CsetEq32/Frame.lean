import N1D226.CsetEq32.Effect
import NativeEntry.Effects
import NativeEntryContract.Core
import Bridge.CruxGenGuarded.QuietTransport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.CsetEq32.Frame
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false

-- The canonical actual prelude supplies these pins; no future guard callback.
theorem guard (s : NativeState) (Rd : BitVec 5) (rd : Rd.toNat < 31) (hp : StepPins s) : N1D226.CsetEq32.Guard s Rd where
  rd := rd
  el := hp.el
  a64 := hp.nrw
  aa64 := hp.f4
  btype := hp.btype
  btn := hp.btn

-- Scalar frame of the SAME actual Sail successor, never expected-state execution.
set_option maxHeartbeats 200000 in
theorem run (s : NativeState) (Rd : BitVec 5) (rd : Rd.toNat < 31) (hp : StepPins s)
    (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_csinc_aarch64_instrs_integer_conditional_select Rd 31#5 1#1 1#4 31#5 0#1 0#1 : SailM Unit) s = .ok () t ∧
      N1D226.CsetEq32.projection t = N1D226.CsetEq32.expected s Rd ∧
      NativeEntryContract.Frame {} s t ∧ HookQuiet ticks t ∧ t.mem = s.mem ∧ t.events = s.events ∧ t.regs.BTypeNext = s.regs.BTypeNext := by
  have hRd : ¬ (Rd.toNat : Int) = 31 := by omega
  obtain ⟨t,run,projection⟩ := N1D226.CsetEq32.effect s Rd (guard s Rd rd hp)
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  have fields : GuardFieldsEq s t := by
    constructor
    all_goals first
      | (rw [regs]; simp only [N1D226.CsetEq32.expected, N1D226.CsetEq32.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd]; done)
      | (rw [regs]; simp [N1D226.CsetEq32.expected, N1D226.CsetEq32.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd] <;> first | rfl | (split <;> first | rfl | simp_all [hp.spe]))
      | (intro k hk; rw [regs]; simp [N1D226.CsetEq32.expected, N1D226.CsetEq32.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd] <;> first | rfl | (split <;> first | rfl | simp_all [hp.spe]))
  have nonProj : Effects.Frame {} s.regs t.regs := by
    change Effects.mask {} t.regs = Effects.mask {} s.regs
    rw [regs]
    simp [N1D226.CsetEq32.expected, N1D226.CsetEq32.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd,Effects.mask] <;> first | rfl | (split <;> first | rfl | simp_all [hp.spe])
  have frame : NativeEntryContract.Frame {} s t := by
    constructor
    all_goals first
      | exact nonProj
      | (rw [regs]; simp [N1D226.CsetEq32.expected, N1D226.CsetEq32.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd] <;> first | rfl | (split <;> first | rfl | simp_all [hp.spe]))
  refine ⟨t,run,projection,frame,quiet_of_fields ticks s t hq fields,?_,?_,?_⟩
  · have mem := congrArg (fun q => q.2.1) projection
    change t.mem = _ at mem
    simpa only [N1D226.CsetEq32.expected, N1D226.CsetEq32.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd] using mem
  · have events := congrArg (fun q => q.2.2) projection
    change t.events = _ at events
    simpa only [N1D226.CsetEq32.expected, N1D226.CsetEq32.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd] using events
  · rw [regs]
    simp [N1D226.CsetEq32.expected, N1D226.CsetEq32.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd] <;> first | rfl | (split <;> first | rfl | simp_all [hp.spe,hp.btn])

#print axioms guard
#print axioms run
end N1D226.CsetEq32.Frame
