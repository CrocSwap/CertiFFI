-- paired-UPDATE route (first-touch tables): each actual walk step's update flag is the
-- table-AF update function of the RAW descriptor present at its slot in a given memory; the
-- leaf step (last) never updates in the walk. Transport across the walk's own table stores at
-- OTHER aligned slots (distinct slots), so all descriptors can be read in the walk's INITIAL memory.
import ArmCertWalk.FinitePathTraceEvents
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 512
namespace ArmCertWalk

/-- Per-step raw descriptors of an actual walk, read in memory `mem`. -/
inductive StepDescs (params : S1TTWParams) (mem : Mem) :
    List (Nat × Bool × Array Event) → List (BitVec 64) → Prop
  | last {pa : Nat} {delta : Array Event} {d : BitVec 64} :
      pa % 8 = 0 → S1ByteMemory.DescAt mem pa d → StepDescs params mem [(pa, false, delta)] [d]
  | table {pa : Nat} {flag : Bool} {delta : Array Event} {d : BitVec 64}
      {rest : List (Nat × Bool × Array Event)} {descs : List (BitVec 64)} :
      pa % 8 = 0 → S1ByteMemory.DescAt mem pa d →
      flag = !decide (S1TableUpdate.word params d = d) →
      StepDescs params mem rest descs → StepDescs params mem ((pa, flag, delta) :: rest) (d :: descs)

theorem desc_at_store_outside (m : S1ByteMemory.Memory) (s0 : Nat) (w : BitVec 64) (pa : Nat) (d : BitVec 64)
    (a0 : s0 % 8 = 0) (a1 : pa % 8 = 0) (ne : pa ≠ s0) :
    S1ByteMemory.DescAt (S1ByteMemory.store m s0 w) pa d ↔ S1ByteMemory.DescAt m pa d := by
  unfold S1ByteMemory.DescAt
  have outside : ∀ i < 8, (S1ByteMemory.store m s0 w)[pa + i]? = m[pa + i]? := by
    intro i hi
    exact S1ByteMemory.lookup_outside m s0 w (pa + i) (by omega)
  constructor
  · intro h i hi; rw [← outside i hi]; exact h i hi
  · intro h i hi; rw [outside i hi]; exact h i hi

theorem desc_at_history_outside {params : S1TTWParams} {footprint : Footprint} {before after : Mem}
    {operations : List TableUpdate} (history : StoreHistory params footprint before operations after)
    (pa : Nat) (d : BitVec 64) (aligned : pa % 8 = 0) (away : ∀ op ∈ operations, op.slot ≠ pa) :
    S1ByteMemory.DescAt after pa d ↔ S1ByteMemory.DescAt before pa d := by
  induction history with
  | nil => exact Iff.rfl
  | cons step tail ih =>
    rw [ih (fun op member => away op (List.mem_cons_of_mem _ member)), step.stored]
    exact desc_at_store_outside _ _ _ pa d step.aligned aligned (fun h => away _ List.mem_cons_self h.symm)

theorem StepDescs.transport {params : S1TTWParams} {m m' : Mem}
    {traffic : List (Nat × Bool × Array Event)} {descs : List (BitVec 64)}
    (h : StepDescs params m' traffic descs)
    (same : ∀ step ∈ traffic, ∀ d, S1ByteMemory.DescAt m' step.1 d → S1ByteMemory.DescAt m step.1 d) :
    StepDescs params m traffic descs := by
  induction h with
  | last aligned present => exact .last aligned (same _ List.mem_cons_self _ present)
  | table aligned present flag _ ih =>
    exact .table aligned (same _ List.mem_cons_self _ present) flag
      (ih (fun step member => same step (List.mem_cons_of_mem _ member)))

theorem StepDescs.slots_aligned {params : S1TTWParams} {m : Mem}
    {traffic : List (Nat × Bool × Array Event)} {descs : List (BitVec 64)}
    (h : StepDescs params m traffic descs) : ∀ step ∈ traffic, step.1 % 8 = 0 := by
  induction h with
  | last aligned _ => intro step member; simp at member; rw [member]; exact aligned
  | table aligned _ _ _ ih =>
    intro step member
    rcases List.mem_cons.mp member with rfl | inner
    · exact aligned
    · exact ih step inner

theorem StepDescs.length_eq {params : S1TTWParams} {m : Mem}
    {traffic : List (Nat × Bool × Array Event)} {descs : List (BitVec 64)}
    (h : StepDescs params m traffic descs) : descs.length = traffic.length := by
  induction h with
  | last _ _ => rfl
  | table _ _ _ _ ih => simp [ih]

theorem StepDescs.congr_haft {p q : S1TTWParams} (haft : p.haft = q.haft) {m : Mem}
    {traffic : List (Nat × Bool × Array Event)} {descs : List (BitVec 64)}
    (h : StepDescs p m traffic descs) : StepDescs q m traffic descs := by
  induction h with
  | last aligned present => exact .last aligned present
  | table aligned present flag _ ih =>
    refine .table aligned present ?_ ih
    rw [flag]; unfold S1TableUpdate.word; rw [haft]

theorem nodup_map_inj {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (eq : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    obtain ⟨fresh, rest⟩ := h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd (eq ▸ List.mem_map_of_mem hb') fresh
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd (eq.symm ▸ List.mem_map_of_mem ha') fresh
      · exact ih rest ha' hb'

#print axioms desc_at_history_outside
#print axioms StepDescs.transport
end ArmCertWalk
