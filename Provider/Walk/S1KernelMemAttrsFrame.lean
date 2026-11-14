import Walk.S1KernelMemAttrs
import Pilot.ObservationSimp
import Walk.S2Frame
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
set_option pp.maxSteps 2000
namespace S1KernelMemAttrsFrame
abbrev State := SequentialState Regs oracleChoiceSource
def Frame (s : State) : EStateM.Result (Sail.Error exception) State MemoryAttributes → Prop
  | .ok _ t => t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events
  | .error _ _ => False
def Valid (attr : BitVec 8) : Prop :=
  attr = 0#8 ∨ attr = 4#8 ∨ attr = 68#8 ∨ attr = 255#8
theorem zero_frame (sh : BitVec 2) (wp : S1TTWParams) (s : State) :
    Frame s (S1KernelMemAttrs.zero_native sh wp s) := by
  observe_simp [Frame, S1KernelMemAttrs.zero_native]
theorem device_frame (sh : BitVec 2) (wp : S1TTWParams) (s : State) :
    Frame s (S1KernelMemAttrs.device_native sh wp s) := by
  observe_simp [Frame, S1KernelMemAttrs.device_native]
theorem uncached_frame (sh : BitVec 2) (wp : S1TTWParams) (s : State) :
    Frame s (S1KernelMemAttrs.uncached_native sh wp s) := by
  observe_simp [Frame, S1KernelMemAttrs.uncached_native]
theorem normal_frame (sh : BitVec 2) (wp : S1TTWParams) (s : State) :
    Frame s (S1KernelMemAttrs.normal_native sh wp s) := by
  observe_simp [Frame, S1KernelMemAttrs.normal_native]

theorem total (attr : BitVec 8) (sh : BitVec 2) (wp : S1TTWParams) (s : State)
    (hValid : Valid attr) :
    ∃ (a : MemoryAttributes) (t : State), S1DecodeMemAttrs attr sh true wp s = .ok a t ∧
      t.regs = s.regs ∧ t.mem = s.mem ∧ t.events = s.events := by
  have hf : Frame s (S1DecodeMemAttrs attr sh true wp s) := by
    rcases hValid with rfl | rfl | rfl | rfl
    · rw [S1KernelMemAttrs.zero_eq]; exact zero_frame sh wp s
    · rw [S1KernelMemAttrs.device_eq]; exact device_frame sh wp s
    · rw [S1KernelMemAttrs.uncached_eq]; exact uncached_frame sh wp s
    · rw [S1KernelMemAttrs.normal_eq]; exact normal_frame sh wp s
  cases hr : S1DecodeMemAttrs attr sh true wp s with
  | error err t => simp only [hr, Frame] at hf
  | ok a t => exact ⟨a, t, rfl, by simpa only [hr, Frame] using hf⟩
#print axioms total
end S1KernelMemAttrsFrame
