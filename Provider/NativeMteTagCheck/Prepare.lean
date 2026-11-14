import NativeMteTagCheck.Primitive
import NativeMte2.Prepare

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false

namespace NativeMteTagCheck
open S1Normality MemM1.NoFault NativeMte2

private def noTopIgnore (address : BitVec 64) : SailM Bool := do
  let state ← readReg Register.PSTATE
  let mtx ← EffectiveMTX address false state.EL
  if mtx == 0#1 then
    let state ← readReg Register.PSTATE
    let tbi ← EffectiveTBI address false state.EL
    pure (tbi == 0#1)
  else pure false

private theorem noTopIgnore_frame (address : BitVec 64) (s : State) (host : HostPins s) :
    ∃ value t, noTopIgnore address s = .ok value t ∧ Frame s t := by
  obtain ⟨mtx, u, hm, fu⟩ := mtx_frame address s host
  obtain ⟨tbi, t, hb, ft⟩ := tbi_frame address u (host.transport fu)
  have hs : (Register.PSTATE.get s.regs).EL = EL0 := host.el
  have hu : (Register.PSTATE.get u.regs).EL = EL0 := (host.transport fu).el
  by_cases equal : (mtx == 0#1) = true
  · exact ⟨tbi == 0#1, t, by
      simp only [noTopIgnore, readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, hs, hu, hm, hb, equal, ite_true], frame_trans fu ft⟩
  · exact ⟨false, u, by
      simp only [noTopIgnore, readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, hs, hm, equal, Bool.false_eq_true, ite_false], fu⟩

private def tagMask (address : BitVec 64) : SailM Bool := do
  let state ← readReg Register.PSTATE
  let tcma ← EffectiveTCMA address state.EL
  let high := Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb address 59 55)
  pure ((tcma == 1#1) && ((high == 0#5) || (high == 31#5)))

private theorem tagMask_frame (address : BitVec 64) (s : State) (host : HostPins s) :
    ∃ value t, tagMask address s = .ok value t ∧ Frame s t := by
  obtain ⟨tcma, t, run, frame⟩ := tcma_frame address s host
  have el : (Register.PSTATE.get s.regs).EL = EL0 := host.el
  unfold tagMask
  simp only [readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, el, run]
  exact ⟨_, t, rfl, frame⟩

theorem store_only_frame (s : State) (host : HostPins s)
    (feature : HaveMTEStoreOnlyExt () s = .ok true s) :
    ∃ value t, StoreOnlyTagCheckingEnabled EL0 s = .ok value t ∧ Frame s t := by
  obtain ⟨unused, u, bits, firstFrame⟩ := bit1 1353 s
  obtain ⟨t, runHost, hostFrame⟩ := host0 u (host.transport firstFrame)
  simp only [Bind.bind, EStateM.bind] at bits
  refine ⟨_get_SCTLR_EL2_Type_TCSO0 (Register.SCTLR_EL2.get t.regs) == 1#1, t, ?_,
    frame_trans firstFrame hostFrame⟩
  simp only [StoreOnlyTagCheckingEnabled, feature, ArmFull.assert, PreSail.assert,
    bits, runHost, readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, beq_self_eq_true,
    Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
  all_goals rfl

private def storeDecision (access : AccessDescriptor) : SailM Bool := do
  let feature ← HaveMTEStoreOnlyExt ()
  if feature && !access.write then StoreOnlyTagCheckingEnabled access.el else pure false

private theorem storeDecision_frame (access : AccessDescriptor) (s : State) (host : HostPins s)
    (el : access.el = EL0) :
    ∃ value t, storeDecision access s = .ok value t ∧ Frame s t := by
  obtain ⟨feature, hf⟩ : ∃ feature, HaveMTEStoreOnlyExt () s = .ok feature s := ⟨_, rfl⟩
  cases feature with
  | false =>
    exact ⟨false, s, by
      simp only [storeDecision, hf, Bool.false_and, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      all_goals rfl, rfl, rfl, rfl⟩
  | true =>
    cases write : access.write with
    | true =>
      exact ⟨false, s, by
        simp only [storeDecision, hf, write, Bool.not_true, Bool.and_false,
          Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
        all_goals rfl, rfl, rfl, rfl⟩
    | false =>
      obtain ⟨value, t, run, frame⟩ := store_only_frame s host hf
      refine ⟨value, t, ?_, frame⟩
      simp only [storeDecision, hf, write, el, run, Bool.not_false, Bool.and_true,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ite_true]

theorem access_default (catalogue : ControlCatalogue) (address : BitVec 64)
    (access : AccessDescriptor) (s : State) (controls : DefaultAt catalogue s)
    (el : access.el = EL0) (requested : access.tagchecked = true) :
    ∃ checked t, AArch64_AccessIsTagChecked address access s = .ok checked t ∧ Frame s t := by
  obtain ⟨ignored, u, hu, fu⟩ := noTopIgnore_frame address s controls.host
  obtain ⟨masked, v, hv, fv⟩ := tagMask_frame address u (controls.host.transport fu)
  have frameSV := frame_trans fu fv
  obtain ⟨enabled, w, hw, fw⟩ := allocation_frame v (controls.host.transport frameSV)
  have frameSW := frame_trans frameSV fw
  obtain ⟨storeOnly, t, ht, ft⟩ := storeDecision_frame access w (controls.host.transport frameSW) el
  have tco : (Register.PSTATE.get w.regs).TCO = 0#1 := (controls.transport frameSW).tco
  have zeroTco : (0#1 == 1#1) = false := rfl
  unfold noTopIgnore at hu
  unfold tagMask at hv
  unfold storeDecision at ht
  simp only [Bind.bind, EStateM.bind, readReg, PreSail.readReg_apply, Pure.pure, EStateM.pure, el] at hu hv ht
  unfold AArch64_AccessIsTagChecked
  cases ignored with
  | true =>
    exact ⟨false, u, by
      simp only [requested, using_a64 s controls.host, ArmFull.assert, PreSail.assert,
        readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        hu, Bool.false_eq_true, ite_true, ite_false], fu⟩
  | false =>
    cases masked with
    | true =>
      exact ⟨false, v, by
        simp only [requested, using_a64 s controls.host, ArmFull.assert, PreSail.assert,
          readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          hu, hv, Bool.false_eq_true, ite_true, ite_false], frameSV⟩
    | false =>
      cases enabled with
      | false =>
        exact ⟨false, w, by
          simp only [requested, el, using_a64 s controls.host, ArmFull.assert, PreSail.assert,
            readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
            hu, hv, hw, Bool.not_false, Bool.false_eq_true, ite_true, ite_false], frameSW⟩
      | true =>
        refine ⟨!storeOnly, t, ?_, frame_trans frameSW ft⟩
        cases storeOnly <;>
          simp only [requested, el, using_a64 s controls.host, ArmFull.assert, PreSail.assert,
            readReg, PreSail.readReg_apply, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
            hu, hv, hw, tco, zeroTco, ht, Bool.not_false, Bool.not_true, Bool.false_eq_true,
            ite_true, ite_false]
        all_goals rfl

theorem prepare_default (catalogue : ControlCatalogue) (address : BitVec 64)
    (access : AccessDescriptor) (s : State) (controls : DefaultAt catalogue s)
    (el : access.el = EL0) :
    ∃ prepared t, NativeMte2.prepare address access s = .ok prepared t ∧
      prepared = { access with tagchecked := prepared.tagchecked } ∧
      Frame s t ∧ DefaultAt catalogue t := by
  cases hm : s.regs.FeatureImpl[134]! with
  | false =>
    refine ⟨access, s, ?_, ?_, ⟨rfl, rfl, rfl⟩, controls⟩
    · simp only [NativeMte2.prepare, NativeMte2.have_mte2, hm, Bool.false_and, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, Bool.false_eq_true, ite_false]
    · cases access; rfl
  | true =>
    cases requested : access.tagchecked with
    | false =>
      refine ⟨access, s, ?_, ?_, ⟨rfl, rfl, rfl⟩, controls⟩
      · simp only [NativeMte2.prepare, NativeMte2.have_mte2, hm, requested,
          Bool.and_false, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
        all_goals rfl
      · cases access
        rfl
    | true =>
      obtain ⟨checked, t, run, frame⟩ := access_default catalogue address access s controls el requested
      refine ⟨{ access with tagchecked := checked }, t, ?_, rfl, frame, controls.transport frame⟩
      simp only [NativeMte2.prepare, NativeMte2.have_mte2, hm, requested, run,
        Bool.and_true, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ite_true]

theorem prepared_kind (access : AccessDescriptor) (checked : Bool) :
    AccessDescriptor_to_Access_kind { access with tagchecked := checked } =
      AccessDescriptor_to_Access_kind access := rfl

#print axioms store_only_frame
#print axioms access_default
#print axioms prepare_default
#print axioms prepared_kind
end NativeMteTagCheck
