import ReleaseProfile.GB10.HeapWorldTables
import ReleaseProfile.GB10.HeapC2World
import ReleaseProfile.GB10.HeapStatics
import ArmCertTranslateModel.HeapV2Initial
import ArmCertTranslateModel.PlanChecks
import ArmCertTranslateModel.HeapV2ShimPlan
import HeapV2StepCerts.CodeScope
import HeapV2Card.Instance

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Heap C2 world: program, memory and caller data

Clean regeneration of the ControlRows world data under release names: VA→PA mapping, pins, code scope, the
four byte-plan segments (image bytes over the scope offsets, shim slot, data ranges, page-table
descriptor bytes) and the entry data part (caller GPRs/SP/PC and the page-table roots, now entry data).
Program/memory/caller data only: no register-file configuration, params, controls or attribute config;
those come from the canonical source (worldEntry = makeModelEntry over the source registers).
-/

namespace ReleaseProfile.GB10.HeapWorldData

open ArmFull ArmCert.Translate ArmCert.Translate.Model ReleaseProfile.GB10 ReleaseProfile.GB10.Heap

/-- Load base (VA of image offset 0). -/
def base : BitVec 64 := 0x400000#64

/-- Image offsets of every byte of every shim code word. -/
def shimOffsets : List Nat :=
  HeapV2ShimPlan.codeWords.flatMap fun c => (List.range 4).map fun i => HeapV2ShimPlan.shimOffset + c.1 + i

/-- VA→PA: each mapped page to its leaf output page (image pages, input/output buffers, stack, shim slot). -/
def mapping : BitVec 64 → Option Nat := fun va =>
  let page := va.toNat / 4096
  let offset := va.toNat % 4096
  if page = 0x400 then some (0x80100000 + offset) else if page = 0x410 then some (0x80110000 + offset)
  else if page = 0x420 then some (0x80120000 + offset) else if page = 0x30 then some (0x80130000 + offset)
  else if page = 0x31 then some (0x80131000 + offset) else if page = 0x1ff then some (0x801ff000 + offset)
  else if page = 0x200 then some (0x80200000 + offset)
  else none

/-- Caller buffers and shim stack: SP 0x200000, x0 0x31000, x1 0x30000. -/
def pins : HeapV2E17.Pins := ⟨0x200000, 0x31000, 0x30000⟩

def imagePlan : List (Nat × BitVec 8) :=
  HeapStatics.imagePlanOf (HeapV2StepCerts.codeOffsets ++ shimOffsets) (HeapV2.image base) base mapping

def slotPlan : List (Nat × BitVec 8) := (List.range 16).map fun i => (0x80200000 + i, 0#8)

/-- Zero bytes over the three data PA ranges (stack page 0x1ff, x0 page 0x31, x1 page 0x30). -/
def dataRanges : List (Nat × Nat) := [(0x80130000, 32), (0x80131000, 32), (0x801fffc0, 64)]
def dataPlan : List (Nat × BitVec 8) := dataRanges.flatMap fun r => (List.range r.2).map fun i => (r.1 + i, 0#8)

def tablePlan : List (Nat × BitVec 8) := imageRowsPlan HeapWorldTables.imageRows

/-! ### Distinct plan addresses by linear checks: each segment strictly increasing, segments in disjoint ranges -/

/-- Adjacent plan addresses strictly increase (a linear check). -/
def sortedB : List (Nat × BitVec 8) → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (a.1 < b.1) && sortedB (b :: t)

theorem sorted_head : ∀ (a : Nat × BitVec 8) (l : List (Nat × BitVec 8)), sortedB (a :: l) = true →
    ∀ c ∈ l, a.1 < c.1
  | _, [], _, c, hc => absurd hc (by simp)
  | a, b :: t, h, c, hc => by
    simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact Nat.lt_trans h.1 (sorted_head b t h.2 c hc)

theorem pairwise_of_sorted : ∀ (l : List (Nat × BitVec 8)), sortedB l = true →
    l.Pairwise (fun a b => (a.1 == b.1) = false)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: t, h => by
    have hrest : sortedB (b :: t) = true := by
      simp only [sortedB, Bool.and_eq_true] at h; exact h.2
    refine List.Pairwise.cons (fun c hc => ?_) (pairwise_of_sorted (b :: t) hrest)
    have := sorted_head a (b :: t) h c hc
    simp only [beq_eq_false_iff_ne, ne_eq]; omega

theorem inRange {l : List (Nat × BitVec 8)} {lo hi : Nat}
    (h : l.all (fun x => decide (lo ≤ x.1) && decide (x.1 < hi)) = true) : ∀ x ∈ l, lo ≤ x.1 ∧ x.1 < hi := by
  intro x hx
  have := List.all_eq_true.1 h x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

theorem image_chain : sortedB imagePlan = true := by decide +kernel
theorem slot_chain : sortedB slotPlan = true := by decide +kernel
theorem data_chain : sortedB dataPlan = true := by decide +kernel
theorem table_chain : sortedB tablePlan = true := by decide +kernel
theorem image_range : imagePlan.all (fun x => decide (0x80100000 ≤ x.1) && decide (x.1 < 0x80121000)) = true := by
  decide +kernel
theorem slot_range : slotPlan.all (fun x => decide (0x80200000 ≤ x.1) && decide (x.1 < 0x80200010)) = true := by
  decide +kernel
theorem data_range : dataPlan.all (fun x => decide (0x80130000 ≤ x.1) && decide (x.1 < 0x80200000)) = true := by
  decide +kernel
theorem table_range : tablePlan.all (fun x => decide (0x80000000 ≤ x.1) && decide (x.1 < 0x80100000)) = true := by
  decide +kernel

theorem planKeys : (imagePlan ++ slotPlan ++ dataPlan ++ tablePlan).Pairwise (fun a b => (a.1 == b.1) = false) := by
  have ri := inRange image_range
  have rs := inRange slot_range
  have rd := inRange data_range
  have rt := inRange table_range
  simp only [List.pairwise_append, List.mem_append]
  refine ⟨⟨⟨pairwise_of_sorted _ image_chain, pairwise_of_sorted _ slot_chain, ?_⟩, pairwise_of_sorted _ data_chain, ?_⟩,
    pairwise_of_sorted _ table_chain, ?_⟩
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

/-- Entry data: caller x0/x1 (buffers), x2 = x3 = 32, x30 = return VA; SP_EL0 = shim SP + 16; PC = shim entry;
page-table roots TTBR0_EL2 = HTTBR = 0x80000000, TTBR1_EL2 = 0. -/
def data : DataPart where
  gpr := Vector.ofFn fun i =>
    if i.val = 0 then 0x31000#64 else if i.val = 1 then 0x30000#64
    else if i.val = 2 then 32#64 else if i.val = 3 then 32#64
    else if i.val = 30 then 0x400000#64 else 0#64
  SP_EL3 := 0#64
  SP_EL2 := 0#64
  SP_EL1 := 0#64
  SP_EL0 := 0x200010#64
  _ZT0 := 0#512
  _ZA := Vector.replicate 256 0#2048
  _FFR := 0#256
  _P := Vector.replicate 16 0#256
  _Z := Vector.replicate 32 0#2048
  PhysicalCount := 0#88
  _PC := 0x410548#64
  TTBR0_EL2 := 0x80000000#128
  TTBR1_EL2 := 0#128
  HTTBR := 0x80000000#64
  timers := fun _ => 0#64

/-- The Heap normal C2 world (program/memory/caller data). -/
def world : HeapWorld where
  imagePlan := imagePlan
  slotPlan := slotPlan
  dataPlan := dataPlan
  tablePlan := tablePlan
  planKeys := planKeys
  mapping := mapping
  pins := pins
  scope := fun o => o ∈ shimOffsets ∨ o ∈ HeapV2StepCerts.codeOffsets
  image := HeapV2.image base
  loadBase := base
  base := base
  offS := HeapV2Card.Instance.offS
  budget := HeapV2Card.Instance.budget
  rows := HeapWorldTables.permissionRows
  data := data

/-- Oracle choices in the Sail-undefined EL2&0 fields (semantics, not configuration): 's values (all zero). -/
def oracle : OracleChoice where
  dc := 0#1
  dct := 0#1
  nv1 := 0#1
  t0sz := 0#3
  t1sz := 0#3
  uwxn := 0#1
  mair2 := 0
  pir := 0
  pire0 := 0
  controlsMair2 := 0#64
  controlsUwxn := false

end ReleaseProfile.GB10.HeapWorldData

#print axioms ReleaseProfile.GB10.HeapWorldData.world
