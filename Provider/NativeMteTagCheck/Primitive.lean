import NativeMte2.Control
import MemM1.MemReadIF
import ArmFull.Fn.M1002

open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option Elab.async false
set_option backward.dsimp.instances true
attribute [local implicit_reducible] oracleChoiceSource

namespace NativeMteTagCheck
open S1Normality MemM1.NoFault
abbrev State := NativeMte2.State

/-- Entry catalogue rows retain the actual preparation control registers. -/
structure ControlCatalogue where
  tcrEL2 : BitVec 64
  sctlrEL2 : BitVec 64
  hcrEL2 : BitVec 64
  scrEL3 : BitVec 64

def PreparationAt (catalogue : ControlCatalogue) (s : State) : Prop :=
  s.regs.bank_BitVec_64 .TCR_EL2 = catalogue.tcrEL2 ∧
  s.regs.bank_BitVec_64 .SCTLR_EL2 = catalogue.sctlrEL2 ∧
  s.regs.bank_BitVec_64 .HCR_EL2 = catalogue.hcrEL2 ∧
  s.regs.bank_BitVec_64 .SCR_EL3 = catalogue.scrEL3

/-- MTE2-agnostic; FEAT_MTE2 (FeatureImpl[134]) may be present or absent. -/
structure DefaultAt (catalogue : ControlCatalogue) (s : State) : Prop where
  host : NativeMte2.HostPins s
  tco : s.regs.PSTATE.TCO = 0#1
  tcf0 : _get_SCTLR_EL2_Type_TCF0 (s.regs.bank_BitVec_64 .SCTLR_EL2) = 0#2
  preparation : PreparationAt catalogue s

protected theorem DefaultAt.transport {catalogue : ControlCatalogue} {s t : State}
    (h : DefaultAt catalogue s) (frame : Frame s t) : DefaultAt catalogue t := by
  refine ⟨h.host.transport frame, ?_, ?_, ?_⟩
  · rw [frame.1]; exact h.tco
  · rw [frame.1]; exact h.tcf0
  · unfold PreparationAt at *
    rw [frame.1]
    exact h.preparation

/-- The actual external-status choice at PhysMemTagRead's labelled occurrence. -/
def TagStatusOK (s : State) : Prop :=
  s.choiceState.1
    (((ChoiceLabel.occ 1354 (s.choiceOcc.getD 1354 0)).child 0).child 0) (.fin 23) = 0

/-- Finite catalogued rows refer to the entry oracle and real occurrence indices. -/
def TagStatusRows (entry : State) (first draws : Nat) : Prop :=
  ∀ index, index < draws → entry.choiceState.1
    (((ChoiceLabel.occ 1354 (first + index)).child 0).child 0) (.fin 23) = 0

/-- This relation must come from execution; the architectural Frame omits it. -/
def ChoiceDelta (s t : State) (draws : Nat) : Prop :=
  t.choiceState.1 = s.choiceState.1 ∧
    t.choiceOcc.getD 1354 0 = s.choiceOcc.getD 1354 0 + draws

theorem choice_delta_refl (s : State) : ChoiceDelta s s 0 := by
  exact ⟨rfl, (Nat.add_zero _).symm⟩

theorem choice_delta_trans {s t u : State} {m n : Nat}
    (first : ChoiceDelta s t m) (second : ChoiceDelta t u n) :
    ChoiceDelta s u (m + n) := by
  refine ⟨second.1.trans first.1, ?_⟩
  rw [second.2, first.2, Nat.add_assoc]

theorem tag_status_transport {s t : State} (delta : ChoiceDelta s t 0)
    (allowed : TagStatusOK s) : TagStatusOK t := by
  unfold TagStatusOK at *
  rw [delta.1, delta.2, Nat.add_zero]
  exact allowed

theorem tag_status_of_rows (entry current : State) (first draws index : Nat)
    (rows : TagStatusRows entry first draws)
    (source : current.choiceState.1 = entry.choiceState.1)
    (occurrenceIndex : current.choiceOcc.getD 1354 0 = first + index)
    (within : index < draws) : TagStatusOK current := by
  unfold TagStatusOK
  rw [source, occurrenceIndex]
  exact rows index within

def advanceOcc (site : Nat) (s : State) : State :=
  { s with choiceOcc := s.choiceOcc.insert site (s.choiceOcc.getD site 0 + 1) }

theorem occurrence (site : Nat) (s : State) :
    (occLabel site : SailM ChoiceLabel) s =
      .ok (.occ site (s.choiceOcc.getD site 0)) (advanceOcc site s) := rfl

theorem advance_frame (site : Nat) (s : State) : Frame s (advanceOcc site s) :=
  ⟨rfl, rfl, rfl⟩

theorem tag_status_advance (site : Nat) (s : State) (different : site ≠ 1354) (h : TagStatusOK s) :
    TagStatusOK (advanceOcc site s) := by
  simpa [TagStatusOK, advanceOcc, Std.ExtHashMap.getD_insert, different, Ne.symm different] using h

theorem fault_none (label : ChoiceLabel) (s : State)
    (selected : s.choiceState.1 (label.child 0) (.fin 23) = 0) :
    undefined_Fault label () s = .ok .Fault_None s := by
  have chosen : (PreSail.chooseAt (.fin 23) (label.child 0) : SailM (Fin 24)) s = .ok 0 s := by
    change EStateM.Result.ok (s.choiceState.1 (label.child 0) (.fin 23)) s = .ok 0 s
    rw [selected]
  unfold undefined_Fault internal_pick_at PreSail.internal_pick_at
  simp only [List.length_cons, List.length_nil, chosen, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure]
  rfl

theorem phys_status_total (label : ChoiceLabel) (s : State) :
    ∃ status, undefined_PhysMemRetStatus label () s = .ok status s := by
  obtain ⟨fault, hf⟩ : ∃ fault, undefined_Fault (label.child 0) () s = .ok fault s := ⟨_, rfl⟩
  obtain ⟨flag, hb⟩ := S1Unknowns.bits_at_total 1 (label.child 1) s
  obtain ⟨error, he⟩ : ∃ error, undefined_ErrorState (label.child 2) () s = .ok error s := ⟨_, rfl⟩
  obtain ⟨store, hs⟩ := S1Unknowns.bits_at_total 64 (label.child 3) s
  refine ⟨⟨fault, flag, error, store⟩, ?_⟩
  simp only [undefined_PhysMemRetStatus, hf, hb, he, hs,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem phys_status_none (label : ChoiceLabel) (s : State)
    (selected : s.choiceState.1 ((label.child 0).child 0) (.fin 23) = 0) :
    ∃ status, undefined_PhysMemRetStatus label () s = .ok status s ∧
      status.statuscode = .Fault_None := by
  have hf := fault_none (label.child 0) s selected
  obtain ⟨flag, hb⟩ := S1Unknowns.bits_at_total 1 (label.child 1) s
  obtain ⟨error, he⟩ : ∃ error, undefined_ErrorState (label.child 2) () s = .ok error s := ⟨_, rfl⟩
  obtain ⟨store, hs⟩ := S1Unknowns.bits_at_total 64 (label.child 3) s
  refine ⟨⟨.Fault_None, flag, error, store⟩, ?_, rfl⟩
  simp only [undefined_PhysMemRetStatus, hf, hb, he, hs,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

/-- Tag reads preserve the event array and retain both real occurrence updates. -/
theorem phys_tag_read_frame (descriptor : AddressDescriptor) (access : AccessDescriptor) (s : State) :
    ∃ status tag, PhysMemTagRead descriptor access s =
      .ok (status, tag) (advanceOcc 1355 (advanceOcc 1354 s)) ∧
      Frame s (advanceOcc 1355 (advanceOcc 1354 s)) := by
  let first := advanceOcc 1354 s
  let label := ChoiceLabel.occ 1354 (s.choiceOcc.getD 1354 0)
  obtain ⟨status, hs⟩ := phys_status_total label first
  let second := advanceOcc 1355 first
  let tagLabel := ChoiceLabel.occ 1355 (first.choiceOcc.getD 1355 0)
  obtain ⟨tag, ht⟩ := S1Unknowns.bits_at_total 4 tagLabel second
  refine ⟨status, tag, ?_, frame_trans (advance_frame 1354 s) (advance_frame 1355 first)⟩
  simp only [PhysMemTagRead, occurrence, hs, ht, first, second, label, tagLabel,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem phys_tag_read_no_fault (descriptor : AddressDescriptor) (access : AccessDescriptor) (s : State)
    (allowed : TagStatusOK s) :
    ∃ status tag, PhysMemTagRead descriptor access s =
      .ok (status, tag) (advanceOcc 1355 (advanceOcc 1354 s)) ∧
      IsFault__2 status = false ∧ Frame s (advanceOcc 1355 (advanceOcc 1354 s)) := by
  let first := advanceOcc 1354 s
  let label := ChoiceLabel.occ 1354 (s.choiceOcc.getD 1354 0)
  obtain ⟨status, hs, hn⟩ := phys_status_none label first allowed
  let second := advanceOcc 1355 first
  let tagLabel := ChoiceLabel.occ 1355 (first.choiceOcc.getD 1355 0)
  obtain ⟨tag, ht⟩ := S1Unknowns.bits_at_total 4 tagLabel second
  refine ⟨status, tag, ?_, ?_, frame_trans (advance_frame 1354 s) (advance_frame 1355 first)⟩
  · simp only [PhysMemTagRead, occurrence, hs, ht, first, second, label, tagLabel,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  · rw [IsFault__2, hn]
    rfl

#print axioms DefaultAt.transport
#print axioms choice_delta_trans
#print axioms tag_status_transport
#print axioms tag_status_of_rows
#print axioms fault_none
#print axioms phys_tag_read_frame
#print axioms phys_tag_read_no_fault
end NativeMteTagCheck
