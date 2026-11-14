import ReleaseProfile.GB10.HeapTrapTables
import ReleaseProfile.GB10.HeapWorldData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Heap trap worlds W_t

Six caller worlds for the Heap trap families `card_initial_t` / `card_ct_t`, t = 0..5 ↔ trap paths
1, 2, 4, 6, 8, 10 (`HeapV2StepCerts.ValBind.TrapPath`). Same image/base/scope/offsets/budget as the normal
world; tables = `HeapTrapTables` (normal + VA page 0); mapping = normal + page 0 → PA 0x80300000.
Caller pins (ControlRows T0..T3): t=0 x0=0; t=1 x1=0; t=2 x0=0x31001; t=3 x1=0x30001; t=4,5 normal pins.
Caller lengths: t=4 x2=16 (path 8: x2 < 32); t=5 x2=32, x3=16 (path 10: 32 ≤ x2, x3 ≠ 32); else 32/32.
Program/memory/caller data only.
-/

namespace ReleaseProfile.GB10.HeapTrapWorld

open ArmFull ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10 ReleaseProfile.GB10.Heap

abbrev T := Fin 6

/-- The trap path selected by world `t`. -/
def path (t : T) : Nat := [1, 2, 4, 6, 8, 10][t.val]

def base : BitVec 64 := HeapWorldData.base

def mapping : BitVec 64 → Option Nat := fun va =>
  if va.toNat / 4096 = 0 then some (0x80300000 + va.toNat % 4096) else HeapWorldData.mapping va

def x0 (t : T) : Nat := if t.val = 0 then 0 else if t.val = 2 then 0x31001 else 0x31000
def x1 (t : T) : Nat := if t.val = 1 then 0 else if t.val = 3 then 0x30001 else 0x30000
def x2 (t : T) : BitVec 64 := if t.val = 4 then 16#64 else 32#64
def x3 (t : T) : BitVec 64 := if t.val = 5 then 16#64 else 32#64

def pins (t : T) : HeapV2E17.Pins := ⟨0x200000, x0 t, x1 t⟩

def imagePlan : List (Nat × BitVec 8) :=
  HeapStatics.imagePlanOf (HeapV2StepCerts.codeOffsets ++ HeapWorldData.shimOffsets) (HeapV2.image base) base mapping

def slotPlan : List (Nat × BitVec 8) := HeapWorldData.slotPlan

/-- PA of a caller buffer VA (pages 0x30/0x31 or page 0). -/
def bufPA (va : Nat) : Nat := ((mapping (BitVec.ofNat 64 va)).getD 0)

/-- Data byte ranges, ascending: x1 buffer, x0 buffer, stack (below the slot), then page 0 (above). -/
def dataRanges (t : T) : List (Nat × Nat) :=
  (if x1 t = 0 then [] else [(bufPA (x1 t), 32)]) ++ (if x0 t = 0 then [] else [(bufPA (x0 t), 32)]) ++
    [(0x801fffc0, 64)] ++ (if x0 t = 0 ∨ x1 t = 0 then [(0x80300000, 32)] else [])

def dataPlan (t : T) : List (Nat × BitVec 8) :=
  (dataRanges t).flatMap fun r => (List.range r.2).map fun i => (r.1 + i, 0#8)

def tablePlan : List (Nat × BitVec 8) := imageRowsPlan HeapTrapTables.imageRows

theorem image_chain : HeapWorldData.sortedB imagePlan = true := by decide +kernel
theorem data_chain : ∀ t : T, HeapWorldData.sortedB (dataPlan t) = true := by decide +kernel
theorem table_chain : HeapWorldData.sortedB tablePlan = true := by decide +kernel
theorem image_range : imagePlan.all (fun x => decide (0x80100000 ≤ x.1) && decide (x.1 < 0x80121000)) = true := by
  decide +kernel
theorem data_range : ∀ t : T, (dataPlan t).all (fun x => (decide (0x80130000 ≤ x.1) && decide (x.1 < 0x80200000)) ||
    (decide (0x80300000 ≤ x.1) && decide (x.1 < 0x80300040))) = true := by
  decide +kernel
theorem table_range : tablePlan.all (fun x => decide (0x80000000 ≤ x.1) && decide (x.1 < 0x80100000)) = true := by
  decide +kernel

theorem inRange2 {l : List (Nat × BitVec 8)} {a b c d : Nat}
    (h : l.all (fun x => (decide (a ≤ x.1) && decide (x.1 < b)) || (decide (c ≤ x.1) && decide (x.1 < d))) = true) :
    ∀ x ∈ l, (a ≤ x.1 ∧ x.1 < b) ∨ (c ≤ x.1 ∧ x.1 < d) := by
  intro x hx
  have := List.all_eq_true.1 h x hx
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

theorem planKeys (t : T) :
    (imagePlan ++ slotPlan ++ dataPlan t ++ tablePlan).Pairwise (fun a b => (a.1 == b.1) = false) := by
  have ri := HeapWorldData.inRange image_range
  have rs := HeapWorldData.inRange HeapWorldData.slot_range
  have rd := inRange2 (data_range t)
  have rt := HeapWorldData.inRange table_range
  simp only [List.pairwise_append, List.mem_append]
  refine ⟨⟨⟨HeapWorldData.pairwise_of_sorted _ image_chain, HeapWorldData.pairwise_of_sorted _ HeapWorldData.slot_chain, ?_⟩,
    HeapWorldData.pairwise_of_sorted _ (data_chain t), ?_⟩, HeapWorldData.pairwise_of_sorted _ table_chain, ?_⟩
  · intro a ha b hb; have := ri a ha; have := rs b hb; simp only [beq_eq_false_iff_ne, ne_eq]; omega
  · intro a ha b hb
    rcases ha with ha | ha
    · have := ri a ha; have := rd b hb; simp only [beq_eq_false_iff_ne, ne_eq]; omega
    · have := rs a ha; have := rd b hb; simp only [beq_eq_false_iff_ne, ne_eq]; omega
  · intro a ha b hb
    have := rt b hb
    rcases ha with (ha | ha) | ha
    · have := ri a ha; simp only [beq_eq_false_iff_ne, ne_eq]; omega
    · have := rs a ha; simp only [beq_eq_false_iff_ne, ne_eq]; omega
    · have := rd a ha; simp only [beq_eq_false_iff_ne, ne_eq]; omega

/-- Entry data of world `t`: caller x0..x3, x30 = return VA; SP/PC/roots as the normal world. -/
def data (t : T) : DataPart :=
  { HeapWorldData.data with
    gpr := Vector.ofFn fun i =>
      if i.val = 0 then BitVec.ofNat 64 (x0 t) else if i.val = 1 then BitVec.ofNat 64 (x1 t)
      else if i.val = 2 then x2 t else if i.val = 3 then x3 t
      else if i.val = 30 then 0x400000#64 else 0#64 }

/-- Heap trap world `t`. -/
def world (t : T) : HeapWorld where
  imagePlan := imagePlan
  slotPlan := slotPlan
  dataPlan := dataPlan t
  tablePlan := tablePlan
  planKeys := planKeys t
  mapping := mapping
  pins := pins t
  scope := fun o => o ∈ HeapWorldData.shimOffsets ∨ o ∈ HeapV2StepCerts.codeOffsets
  image := HeapV2.image base
  loadBase := base
  base := base
  offS := HeapV2Card.Instance.offS
  budget := HeapV2Card.Instance.budget
  rows := HeapTrapTables.permissionRows
  data := data t

theorem imagePlan_eq : imagePlan =
    HeapStatics.imagePlanOf (HeapV2StepCerts.codeOffsets ++ HeapWorldData.shimOffsets) (HeapV2.image base) base mapping := by
  unfold imagePlan; rfl

theorem world_imagePlan (t : T) : (world t).imagePlan =
    HeapStatics.imagePlanOf (HeapV2StepCerts.codeOffsets ++ HeapWorldData.shimOffsets) (HeapV2.image (world t).base)
      (world t).base (world t).mapping := by
  show imagePlan = _
  exact imagePlan_eq

end ReleaseProfile.GB10.HeapTrapWorld

#print axioms ReleaseProfile.GB10.HeapTrapWorld.world
