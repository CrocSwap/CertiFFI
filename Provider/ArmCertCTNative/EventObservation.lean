import Sail.ConcurrencyInterfaceV1

/-!
# Native per-step observation from the provider event log

The frozen provider Sail (provider, fork H3) appends every architectural side
effect to `SequentialState.events` in program order; `sail_mem_read`/`sail_mem_write`
log `memRead`/`memWrite` with physical address, size, optional virtual address, access
kind and (writes) the value, at request time.

The native data observation of one step is the event DELTA, projected:
* explicit (`AK_explicit`) reads/writes with a virtual address become
  `{kind, address := va, size}`, mirroring CertiFFI `DataAccess` field for field.
  Values and tags are DROPPED: CT observations carry no data.
* instruction-fetch reads, translation-walk reads and translation start/end are
  `derived`: kept whole in the native observation, and per form shown to be a fixed
  public function of (PC, data accesses) under the admitted page map;
* everything else is `other` and must be shown ABSENT per form (`NoOtherEvents`):
  `AK_arch`, barriers, cache ops, TLBI, takeException/returnException (faults are
  excluded in admitted runs), explicit accesses without a VA.
Events semantics: provider Sail/Sail/ConcurrencyInterfaceV1.lean sha256 fdfab689
(provider receipt 44ce1173, step-boundary seal f1f701c8).
-/

open Sail.ConcurrencyInterfaceV1

namespace ArmCertCT.Native

inductive AccessKind where
  | read | write
  deriving DecidableEq, Repr

/-- Mirrors `CertiFFI.AArch64.DataAccess` (CertiFFI 62329679, Core/Access.lean:21). -/
structure DataAccess where
  kind : AccessKind
  address : BitVec 64
  size : Nat
  deriving DecidableEq, Repr

/-- `derived`: instruction-fetch reads, translation-table-walk reads and
translation start/end events. They are kept in the native observation and must be
shown to be a fixed PUBLIC function of the step's PC and data accesses under the
admitted page map (defects 3869 (a)); they are never silently dropped. -/
inductive Projected where
  | access (a : DataAccess)
  | derived
  | other
  deriving DecidableEq, Repr

variable [Arch]

def projectEvent : Event → Projected
  | .memRead _ size (some va) (.AK_explicit _) _ =>
      .access { kind := .read, address := BitVec.ofNat 64 va, size }
  | .memWrite _ size (some va) (.AK_explicit _) _ _ =>
      .access { kind := .write, address := BitVec.ofNat 64 va, size }
  | .memRead _ _ _ (.AK_ifetch _) _ => .derived
  | .memRead _ _ _ (.AK_ttw _) _ => .derived
  | .translationStart _ => .derived
  | .translationEnd _ => .derived
  | _ => .other

/-- The events a step appended: `s'.events = s.events ++ delta`. -/
def Appended {R : Type} {c : ChoiceSource} (s s' : SequentialState R c) (delta : Array Event) : Prop :=
  s'.events = s.events ++ delta

def accessesOf (delta : Array Event) : List DataAccess :=
  delta.toList.filterMap fun e => match projectEvent e with
    | .access a => some a
    | _ => none

inductive DerivedKind where
  | ttw | ifetch | translationStart | translationEnd
  deriving DecidableEq, Repr

/-- Projected derived record (defects 85f6/98aa option 2): physical address, size
and kind only. DROPPED, with justification:
* the `va` field of a walk/fetch read: eval m1a v14 leaves it existential in
  `IsTTWRead`; it is the request's walk-VA, a function of the translated VA, which is
  already in the observation (fetch: `pc`; data: `DataAccess.address`). Dropping it
  removes no information about secrets beyond what `pc`/addresses expose.
* the `tag` request flag: pinned `false` for walk reads (m1a v14); MTE tag requests are
  absent under the profile.
* translationStart/End payloads (TranslationStartInfo / AddressDescriptor): VA, regime,
  ASID/VMID, attributes and the result PA. They are not memory traffic; the PA is already
  carried by the subsequent read's `pa`, and the rest is profile-pinned or VA-derived.
  These events are kept as kind-only markers, so their COUNT and ORDER stay observable.
  CONDITION (defects f30d6fe2): dropping the translationEnd FaultRecord/result is sound ONLY
  because admitted runs are fault-free (no takeException; faults excluded by admission); the
  CT headline must state this. -/
structure DerivedRec where
  pa : Nat
  size : Nat
  kind : DerivedKind
  deriving DecidableEq, Repr

def derivedRec : Event → Option DerivedRec
  | .memRead pa size _ (.AK_ttw _) _ => some ⟨pa, size, .ttw⟩
  | .memRead pa size _ (.AK_ifetch _) _ => some ⟨pa, size, .ifetch⟩
  | .translationStart _ => some ⟨0, 0, .translationStart⟩
  | .translationEnd _ => some ⟨0, 0, .translationEnd⟩
  | _ => none

/-- Derived records of the delta, in order. -/
def derivedOf (delta : Array Event) : List DerivedRec :=
  delta.toList.filterMap derivedRec

/-- a design decision (supersedes 65): merge adjacent same-kind CONTIGUOUS explicit accesses of one
instruction into one access, so the model's split of a pair (1x16, 2x8 or byte-wise, memory
PairShapes) matches CertiFFI's single {addr, n} access. The split is a function of the public
base address. Non-contiguous or mixed-kind accesses are left separate (fail closed downstream). -/
def mergeContig : List DataAccess → List DataAccess
  | x :: y :: rest =>
      if y.kind = x.kind ∧ y.address = x.address + BitVec.ofNat 64 x.size then
        mergeContig ({ x with size := x.size + y.size } :: rest)
      else x :: mergeContig (y :: rest)
  | l => l
termination_by l => l.length

/-- The native data observation of a step: merged explicit accesses. -/
def obsAccesses (delta : Array Event) : List DataAccess := mergeContig (accessesOf delta)

theorem mergeContig_nil : mergeContig [] = [] := by simp [mergeContig]
theorem mergeContig_single (x : DataAccess) : mergeContig [x] = [x] := by simp [mergeContig]

/-- 2x8 pair split (memory readV5_ldp8 / stpV5_8) merges to CertiFFI's single 16-byte access. -/
theorem mergeContig_pair8 (k : AccessKind) (a : BitVec 64) :
    mergeContig [⟨k, a, 8⟩, ⟨k, a + 8, 8⟩] = [⟨k, a, 16⟩] := by
  simp [mergeContig]

def NoOtherEvents (delta : Array Event) : Prop :=
  ∀ e ∈ delta.toList, projectEvent e ≠ .other

/-- The appended delta is determined by the pre- and post-state (append-only log). -/
theorem appended_unique {R : Type} {c : ChoiceSource} {s s' : SequentialState R c}
    {d₁ d₂ : Array Event} (h₁ : Appended s s' d₁) (h₂ : Appended s s' d₂) : d₁ = d₂ := by
  unfold Appended at h₁ h₂
  have h := h₁.symm.trans h₂
  have := congrArg Array.toList h
  simp only [Array.toList_append] at this
  exact Array.toList_inj.mp (List.append_cancel_left this)

/-- Register-only forms: an empty delta gives no data accesses and no other events. -/
theorem accessesOf_empty : accessesOf (#[] : Array Event) = [] := rfl
theorem noOther_empty : NoOtherEvents (#[] : Array Event) := by
  intro e he; simp at he

/-- Value-independence: the projection of a write ignores the value written. -/
theorem projectEvent_write_value_free (pa size va : Nat) (k : Explicit_access_kind)
    (v₁ v₂ : Option (BitVec (8 * size))) (t₁ t₂ : Option Bool) :
    projectEvent (.memWrite pa size (some va) (.AK_explicit k) v₁ t₁) =
      projectEvent (.memWrite pa size (some va) (.AK_explicit k) v₂ t₂) := rfl

/-- eval m1a v14 IsTTWRead shape (AK_ttw, tag false): always `derived`. -/
theorem ttw_read_derived (pa size : Nat) (va : Option Nat) (u : Unit) (tag : Bool) :
    projectEvent (.memRead pa size va (.AK_ttw u) tag) = .derived := by
  cases va <;> rfl

/-- The instruction-fetch read (AK_ifetch): always `derived`. -/
theorem ifetch_read_derived (pa size : Nat) (va : Option Nat) (u : Unit) (tag : Bool) :
    projectEvent (.memRead pa size va (.AK_ifetch u) tag) = .derived := by
  cases va <;> rfl

theorem translationStart_derived (ts : Arch.trans_start) :
    projectEvent (.translationStart ts) = .derived := rfl
theorem translationEnd_derived (te : Arch.trans_end) :
    projectEvent (.translationEnd te) = .derived := rfl

end ArmCertCT.Native

#print axioms ArmCertCT.Native.appended_unique
#print axioms ArmCertCT.Native.projectEvent_write_value_free
