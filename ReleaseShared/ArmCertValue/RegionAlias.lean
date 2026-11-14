-- a design decision: exact aliases share one canonical byte inventory before SSA compilation.
import ArmCertValue.FMemory
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace ArmCertValue.RegionAlias
open HeapV2StepCerts.RegBind (St)
open Physical (BytePA)

/-- Renaming only: offsets are preserved, so this represents exact whole-region aliasing. -/
def merge (input output r : Region) : Region := if r = input then output else r

theorem merge_idempotent (input output r : Region) :
    merge input output (merge input output r) = merge input output r := by
  by_cases h : r = input
  · subst r
    by_cases same : output = input <;> simp [merge,same]
  · simp [merge,h]

theorem merge_words (input output r : Region) (same : input.words = output.words) :
    (merge input output r).words = r.words := by
  by_cases h : r = input
  · subst r;simp [merge,same]
  · simp [merge,h]

/-- A normalized region list has a single entry for each shared storage region. -/
def regions (norm : Region → Region) (rs : List Region) : List Region := (rs.map norm).eraseDups

theorem region_mem (norm : Region → Region) (rs : List Region) (r : Region) (hr : r ∈ rs) :
    norm r ∈ regions norm rs := by
  simp only [regions,List.mem_eraseDups,List.mem_map]
  exact ⟨r,hr,rfl⟩

theorem regions_fixed (norm : Region → Region) (idem : ∀ r, norm (norm r) = norm r)
    (rs : List Region) (r : Region) (hr : r ∈ regions norm rs) : norm r = r := by
  simp only [regions,List.mem_eraseDups,List.mem_map] at hr
  obtain ⟨q,hq,rfl⟩ := hr
  exact idem q

/-- Normalize every memory operand before invoking the existing compiler. -/
def effect (norm : Region → Region) : MemEff → MemEff
  | .load rt r i => .load rt (norm r) i
  | .store rt r i => .store rt (norm r) i
  | .loadb rt r i => .loadb rt (norm r) i
  | .storeb rt r i => .storeb rt (norm r) i
  | .load32 rt r i => .load32 rt (norm r) i
  | .store32 rt r i => .store32 rt (norm r) i

def step (norm : Region → Region) : F.Step → F.Step
  | .legacy s => .legacy {s with mem := s.mem.map (effect norm)}
  | .store width source r j => .store width source (norm r) j

def plan (norm : Region → Region) (steps : List F.Step) : List F.Step := steps.map (step norm)

theorem effect_idempotent (norm : Region → Region) (idem : ∀ r, norm (norm r) = norm r)
    (e : MemEff) : effect norm (effect norm e) = effect norm e := by
  cases e <;> simp only [effect,idem]

theorem step_idempotent (norm : Region → Region) (idem : ∀ r, norm (norm r) = norm r)
    (s : F.Step) : step norm (step norm s) = step norm s := by
  cases s with
  | legacy s =>
    simp only [step,List.map_map]
    congr 2
    exact List.map_congr_left (fun e _ => effect_idempotent norm idem e)
  | store width source r j => simp only [step,idem]

theorem plan_length (norm : Region → Region) (steps : List F.Step) :
    (plan norm steps).length = steps.length := List.length_map _

/-- Pull a symbolic byte view back to every original name, using the SAME SSA slot for aliases. -/
def expand (norm : Region → Region) (s : Sym) : Sym :=
  {s with memB := fun r j => s.memB (norm r) j}

/-- Physical views agree for every byte; names alone never create fresh storage. -/
def ViewAgrees (norm : Region → Region) (view : BytePA) : Prop :=
  ∀ r j, view r j = view (norm r) j

theorem read_normalized (norm : Region → Region) (view : BytePA) (agree : ViewAgrees norm view)
    (s : St) (r : Region) (j : Nat) :
    Physical.regionByte view s r j = Physical.regionByte view s (norm r) j := by
  unfold Physical.regionByte
  rw [agree r j]

theorem expand_agrees (norm : Region → Region) (view : BytePA) (agree : ViewAgrees norm view)
    (vals : List (BitVec 64)) (s : Sym) (x : St) (h : Physical.Agrees view vals s x) :
    Physical.Agrees view vals (expand norm s) x := by
  refine ⟨h.1,h.2.1,?_⟩
  intro r j i k hs
  rw [read_normalized norm view agree x r j]
  exact h.2.2 (norm r) j i k hs

theorem expand_bounded (norm : Region → Region) (s : Sym) (n : Nat) (h : s.Bounded n) :
    (expand norm s).Bounded n := by
  exact ⟨h.1,h.2.1,fun r j i k hs => h.2.2 (norm r) j i k hs⟩

theorem word_normalized (norm : Region → Region) (view : BytePA) (agree : ViewAgrees norm view)
    (s : St) (r : Region) (w : Nat) :
    Physical.regionWord view s r w = Physical.regionWord view s (norm r) w := by
  unfold Physical.regionWord
  congr 1
  funext j acc
  rw [read_normalized norm view agree s r (8*w+j)]

/-- On expanded views a canonical store updates every aliased name to the new value. -/
theorem store_alias_slot (norm : Region → Region) (s : Sym) (id : Nat) (rs : List Region)
    (r q : Region) (j width t : Nat) (member : norm r ∈ rs)
    (fits : j + width ≤ 8 * (norm r).words) (same : norm q = norm r) (ht : t < width) :
    (expand norm (F.storeMap s id rs (norm r) j width)).memB q (j+t) = some (id,t) := by
  simp only [expand,F.storeMap,same]
  rw [if_pos ⟨member,by omega⟩,if_pos ⟨rfl,by omega,by omega⟩]
  congr 2
  omega

/-- A source layout with equal base addresses gives identical byte views for I=O. -/
theorem merge_view (input output : Region) (pinv : Nat → Nat) (mapping : BitVec 64 → Option Nat)
    (base : (pinv input.pin : Int) + input.off = (pinv output.pin : Int) + output.off) :
    ViewAgrees (merge input output) (fun r j => mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + j))) := by
  intro r j
  by_cases h : r = input
  · subst r;simp [merge,base]
  · simp only [merge,if_neg h]

/-- All aliases preserve the complete region base/size. Distinct canonical bytes remain physically distinct.
This admits exact sharing and excludes partial overlap through the canonical injectivity field. -/
structure Layout (norm : Region → Region) (pinv : Nat → Nat) (rs : List Region) (view : BytePA) : Prop where
  idempotent : ∀ r, norm (norm r) = norm r
  words : ∀ r, (norm r).words = r.words
  base : ∀ r, (pinv r.pin : Int) + r.off = (pinv (norm r).pin : Int) + (norm r).off
  viewEq : ViewAgrees norm view
  injective : Physical.RegionsInjective view (regions norm rs)

/-- Original machine access addresses equal normalized value addresses at every offset. -/
theorem same_va (norm : Region → Region) (pinv : Nat → Nat) (r : Region) (offset : Int)
    (base : (pinv r.pin : Int) + r.off = (pinv (norm r).pin : Int) + (norm r).off) :
    BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + offset) =
    BitVec.ofInt 64 ((pinv (norm r).pin : Int) + (norm r).off + offset) := by rw [base]

theorem view_of_bases (norm : Region → Region) (pinv : Nat → Nat) (mapping : BitVec 64 → Option Nat)
    (base : ∀ r, (pinv r.pin : Int) + r.off = (pinv (norm r).pin : Int) + (norm r).off) :
    ViewAgrees norm (fun r j => mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + j))) := by
  intro r j
  dsimp only
  rw [base r]

/-- Actual Sail write payloads use the existing frame adapter on the unique canonical byte inventory. -/
theorem normalized_store (norm : Region → Region) (pinv : Nat → Nat) (rs : List Region)
    (view : BytePA) (layout : Layout norm pinv rs view) (x y : St) (width : Nat) (u : VUpd)
    (r : Region) (j pa : Nat) (value : BitVec (8*width)) (member : r ∈ rs)
    (fits : j+width ≤ 8*r.words)
    (span : ∀ t, t < width → view r (j+t) = some (pa+t))
    (bytes : ∀ t, t < width → value.extractLsb' (8*t) 8 = ((u.eval x) >>> (8*t)).setWidth 8)
    (write : y.mem = MemM1.MemWriteD1.wfold x.mem pa width (fun t => value.extractLsb' (8*t) 8)) :
    F.StoreHolds view (regions norm rs) width u (norm r) j x y := by
  apply F.storeHolds_of_wfold view (regions norm rs) x y width u (norm r) j pa value
    (region_mem norm rs r member)
  · rw [layout.words];exact fits
  · intro t ht
    rw [←layout.viewEq r (j+t)]
    exact span t ht
  · exact layout.injective
  · exact bytes
  · exact write

/-- Frame only canonical storage. Aliased input names acquire the output's new bytes. -/
theorem frame_alias (norm : Region → Region) (view : BytePA) (agree : ViewAgrees norm view)
    (x y : St) (r : Region) (j : Nat)
    (frame : Physical.regionByte view y (norm r) j = Physical.regionByte view x (norm r) j) :
    Physical.regionByte view y r j = Physical.regionByte view x r j := by
  rw [read_normalized norm view agree y,read_normalized norm view agree x]
  exact frame

#print axioms normalized_store
#print axioms same_va
#print axioms step_idempotent
#print axioms word_normalized
#print axioms merge_idempotent
#print axioms expand_agrees
#print axioms store_alias_slot
#print axioms merge_view
end ArmCertValue.RegionAlias
