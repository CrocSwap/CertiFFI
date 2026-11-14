import N1D226.CsnegCs64Generic.Effect
import NativeEntry.Effects
import NativeEntryContract.Core
import Bridge.CruxGenGuarded.QuietTransport
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
namespace N1D226.CsnegCs64Generic.Frame
open ArmBridge.Draft ArmBridge.CruxCore ArmBridge.CruxGenGuarded NativeEntry
open ArmCert.HookQuiet.V0 (HookQuiet)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option Elab.async false

-- The canonical actual prelude supplies these pins; no future guard callback.
theorem guard (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (hp : StepPins s) : N1D226.CsnegCs64Generic.Guard s Rd Rn Rm where
  rd := rd
  rn := rn
  rm := rm
  el := hp.el
  a64 := hp.nrw
  aa64 := hp.f4
  btype := hp.btype
  btn := hp.btn

-- Scalar frame of the SAME actual Sail successor, never expected-state execution.
set_option maxHeartbeats 200000 in
theorem run (s : NativeState) (Rd : BitVec 5) (Rn : BitVec 5) (Rm : BitVec 5) (rd : Rd.toNat < 31) (rn : Rn.toNat < 31) (rm : Rm.toNat < 31) (hp : StepPins s)
    (ticks : Nat) (hq : HookQuiet ticks s) :
    ∃ t, (decode_csneg_aarch64_instrs_integer_conditional_select Rd Rn 1#1 2#4 Rm 1#1 1#1 : SailM Unit) s = .ok () t ∧
      N1D226.CsnegCs64Generic.projection t = N1D226.CsnegCs64Generic.expected s Rd Rn Rm ∧
      NativeEntryContract.Frame {} s t ∧ HookQuiet ticks t ∧ t.mem = s.mem ∧ t.events = s.events ∧ t.regs.BTypeNext = s.regs.BTypeNext := by
  have hRd : ¬ (Rd.toNat : Int) = 31 := by omega
  have hRn : ¬ (Rn.toNat : Int) = 31 := by omega
  have hRm : ¬ (Rm.toNat : Int) = 31 := by omega
  obtain ⟨t,run,projection⟩ := N1D226.CsnegCs64Generic.effect s Rd Rn Rm (guard s Rd Rn Rm rd rn rm hp)
  have regs := congrArg Prod.fst projection
  change t.regs = _ at regs
  have fields : GuardFieldsEq s t := by
    constructor
    all_goals first
      | (rw [regs]; simp only [N1D226.CsnegCs64Generic.expected, N1D226.CsnegCs64Generic.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd, hRn, hRm]; done)
      | (rw [regs]; simp [N1D226.CsnegCs64Generic.expected, N1D226.CsnegCs64Generic.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd, hRn, hRm] <;> first | rfl | (split <;> first | rfl | simp_all [hp.spe]))
      | (intro k hk; rw [regs]; simp [N1D226.CsnegCs64Generic.expected, N1D226.CsnegCs64Generic.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd, hRn, hRm] <;> first | rfl | (split <;> first | rfl | simp_all [hp.spe]))
  have nonProj : Effects.Frame {} s.regs t.regs := by
    change Effects.mask {} t.regs = Effects.mask {} s.regs
    rw [regs]
    simp [N1D226.CsnegCs64Generic.expected, N1D226.CsnegCs64Generic.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd, hRn, hRm,Effects.mask] <;> first | rfl | (split <;> first | rfl | simp_all [hp.spe])
  have frame : NativeEntryContract.Frame {} s t := by
    constructor
    all_goals first
      | exact nonProj
      | (rw [regs]; simp [N1D226.CsnegCs64Generic.expected, N1D226.CsnegCs64Generic.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd, hRn, hRm] <;> first | rfl | (split <;> first | rfl | simp_all [hp.spe]))
  refine ⟨t,run,projection,frame,quiet_of_fields ticks s t hq fields,?_,?_,?_⟩
  · have mem := congrArg (fun q => q.2.1) projection
    change t.mem = _ at mem
    simpa only [N1D226.CsnegCs64Generic.expected, N1D226.CsnegCs64Generic.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd, hRn, hRm] using mem
  · have events := congrArg (fun q => q.2.2) projection
    change t.events = _ at events
    simpa only [N1D226.CsnegCs64Generic.expected, N1D226.CsnegCs64Generic.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd, hRn, hRm] using events
  · rw [regs]
    simp [N1D226.CsnegCs64Generic.expected, N1D226.CsnegCs64Generic.effect_native, hp.spe, hp.btn, apply_ite, ite_self, hRd, hRn, hRm] <;> first | rfl | (split <;> first | rfl | simp_all [hp.spe,hp.btn])

#print axioms guard
#print axioms run
end N1D226.CsnegCs64Generic.Frame
