-- Route 7 breadth: memmove deployment context (loops CopyNative.Context WITHOUT the disjointness field),
-- the path decided by the binary (CBZ / CMP+B.EQ / B.LO), and the environment over Runtime InvG.
import Route7Copy.Context
import ArmCertLoop.CopyGeometry
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 8192
set_option Elab.async false

namespace Route7Move
open ArmCertLoop ArmCertLoop.ContractDraft

/-- memmove deployment: the memcpy context minus `disjoint` (the spans may overlap). -/
structure Context where
  domain : QueryDomain
  spec : TopologyImageSpec domain
  config : AttributeConfig
  rows : List PermissionRow
  mapping : BitVec 64 → Option Nat
  base : BitVec 64
  d : BitVec 64
  s : BitVec 64
  returnPC : BitVec 64
  n : Nat
  page : base.toNat % 4096 = 0
  low : base.toNat < 2 ^ 54
  returnLow : returnPC.toNat < 2 ^ 54
  sourceObject : SpanMap.NoWrap (sourceSpan s n)
  destObject : SpanMap.NoWrap (destSpan d n)
  code : CodeGeometry mapping base
  codeWrite : CodeWriteSeparated mapping base d n
  data : DataGeometry mapping d s n (rowsFootprint spec.imageRows).byte
  injective : SpanMap.UnionInjective mapping (spans d s n)
  separated : ImageTableSeparated codeScope base mapping (rowsFootprint spec.imageRows).byte

/-- The path the binary takes (CBZ x2; CMP x0,x1; B.EQ; B.LO), a function of the public arguments. -/
def movePath (d s : BitVec 64) (n : Nat) : Schedule.MovePath :=
  if n = 0 then .empty else if d = s then .same else if d.toNat < s.toNat then .forward else .backward

def Context.path (c : Context) : Schedule.MovePath := movePath c.d c.s c.n
def Context.budget (c : Context) : Nat := Schedule.moveSteps c.path c.n
def Context.consumer (c : Context) :=
  SpanMap.consumerMap (spans c.d c.s c.n) (Image.codeVAs c.base Generated.imageStart Generated.imageWords)
    c.mapping (rowsFootprint c.spec.imageRows).byte
def Context.srcPA (c : Context) (i : Nat) : Nat := (c.mapping (c.s + BitVec.ofNat 64 i)).getD 0
def Context.dstPA (c : Context) (i : Nat) : Nat := (c.mapping (c.d + BitVec.ofNat 64 i)).getD 0
def offset (c : Context) : Nat → BitVec 64 :=
  Schedule.nativeOffset c.base c.returnPC c.budget
    (fun k => Generated.armcert_memmove_entry + Schedule.moveWordOffset c.path c.n k)

/-- Memory steps: forward LDRB/STRB at 5 + 6i + {0,1}; backward at 6 + 6i + {2,3} (i < n). -/
def memStep (p : Schedule.MovePath) (n k : Nat) : Bool :=
  match p with
  | .forward => decide (5 ≤ k ∧ (k - 5) % 6 < 2 ∧ (k - 5) / 6 < n)
  | .backward => decide (6 ≤ k ∧ 2 ≤ (k - 6) % 6 ∧ (k - 6) % 6 < 4 ∧ (k - 6) / 6 < n)
  | _ => false

def movePast (p : Schedule.MovePath) (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => movePast p n k + (if memStep p n k then 1 else 0)

theorem movePast_succ (p : Schedule.MovePath) (n k : Nat) :
    movePast p n (k + 1) = movePast p n k + (if memStep p n k then 1 else 0) := rfl

/-- The memmove environment: Runtime InvG over the memmove context, tag-status capacity 2n. -/
abbrev EnvM (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k : Nat) (x : NativeState) : Prop :=
  ReleaseProfile.DefaultRuntime.InvG c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.base
    (offset c) c.budget (fun _ _ => True) catalogue entry (2 * c.n) (movePast c.path c.n) k x

theorem source_mapped (c : Context) (i : Nat) (room : i < c.n) :
    ∃ pa : BitVec 56, c.mapping (c.s + BitVec.ofNat 64 i) = some pa.toNat ∧
      MemM1.MemReadIF.NotMMIO pa ∧ ¬ (rowsFootprint c.spec.imageRows).byte pa.toNat := by
  simpa only [sourceSpan, SpanMap.byteVA] using c.data (sourceSpan c.s c.n) (by simp [spans]) i room

theorem dest_mapped (c : Context) (i : Nat) (room : i < c.n) :
    ∃ pa : BitVec 56, c.mapping (c.d + BitVec.ofNat 64 i) = some pa.toNat ∧
      MemM1.MemReadIF.NotMMIO pa ∧ ¬ (rowsFootprint c.spec.imageRows).byte pa.toNat := by
  simpa only [destSpan, SpanMap.byteVA] using c.data (destSpan c.d c.n) (by simp [spans]) i room

theorem dest_distinct (c : Context) (i j : Nat) (ir : i < c.n) (jr : j < c.n) (different : j ≠ i) :
    c.dstPA j ≠ c.dstPA i := by
  obtain ⟨pa, ma, _, _⟩ := dest_mapped c j jr
  obtain ⟨pb, mb, _, _⟩ := dest_mapped c i ir
  apply SpanMap.mapped_different c.mapping (spans c.d c.s c.n) c.injective _ _
    ⟨destSpan c.d c.n, by simp [spans], j, jr, rfl⟩
    ⟨destSpan c.d c.n, by simp [spans], i, ir, rfl⟩ ⟨pa.toNat, ma⟩ ⟨pb.toNat, mb⟩
  intro same
  have equal := congrArg BitVec.toNat same
  rw [SpanMap.byteVA_toNat (destSpan c.d c.n) c.destObject j jr,
    SpanMap.byteVA_toNat (destSpan c.d c.n) c.destObject i ir] at equal
  exact different (by omega)

/-- Source byte j and destination byte i are physically distinct whenever their virtual addresses differ
(UnionInjective over the union of the two spans; overlap is allowed, aliasing of distinct VAs is not). -/
theorem source_dest_distinct_of (c : Context) (i j : Nat) (ir : i < c.n) (jr : j < c.n)
    (va : c.s.toNat + j ≠ c.d.toNat + i) : c.srcPA j ≠ c.dstPA i := by
  obtain ⟨pa, ma, _, _⟩ := source_mapped c j jr
  obtain ⟨pb, mb, _, _⟩ := dest_mapped c i ir
  apply SpanMap.mapped_different c.mapping (spans c.d c.s c.n) c.injective _ _
    ⟨sourceSpan c.s c.n, by simp [spans], j, jr, rfl⟩
    ⟨destSpan c.d c.n, by simp [spans], i, ir, rfl⟩ ⟨pa.toNat, ma⟩ ⟨pb.toNat, mb⟩
  intro same
  have equal := congrArg BitVec.toNat same
  rw [SpanMap.byteVA_toNat (sourceSpan c.s c.n) c.sourceObject j jr,
    SpanMap.byteVA_toNat (destSpan c.d c.n) c.destObject i ir] at equal
  simp only [sourceSpan, destSpan] at equal
  exact va equal

/-- Forward overlap: with d <u s, a source byte after i never aliases destination byte i. -/
theorem forward_future (c : Context) (lt : c.d.toNat < c.s.toNat) (i j : Nat) (ir : i < c.n) (gt : i < j) (jr : j < c.n) :
    c.srcPA j ≠ c.dstPA i :=
  source_dest_distinct_of c i j ir jr (by omega)

/-- Backward overlap (reversed index t ↦ n-1-t): with s <u d, a source byte read later (lower index) never aliases
the destination byte being written. -/
theorem backward_future (c : Context) (gt : c.s.toNat < c.d.toNat) (t u : Nat) (tr : t < c.n) (later : t < u) (ur : u < c.n) :
    c.srcPA (c.n - 1 - u) ≠ c.dstPA (c.n - 1 - t) :=
  source_dest_distinct_of c (c.n - 1 - t) (c.n - 1 - u) (by omega) (by omega) (by omega)

/-! ## Path offsets -/

theorem path_forward (c : Context) (nz : c.n ≠ 0) (ne : c.d ≠ c.s) (lt : c.d.toNat < c.s.toNat) :
    c.path = .forward := by
  simp only [Context.path, movePath, if_neg nz, if_neg ne, if_pos lt]

theorem path_backward (c : Context) (nz : c.n ≠ 0) (ne : c.d ≠ c.s) (ge : ¬ c.d.toNat < c.s.toNat) :
    c.path = .backward := by
  simp only [Context.path, movePath, if_neg nz, if_neg ne, if_neg ge]

theorem forward_loop_offset (n i j : Nat) (room : i < n) (slot : j < 6) :
    Schedule.moveWordOffset .forward n (5 + 6 * i + j) = 56 + 4 * j := by
  simp only [Schedule.moveWordOffset]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 2
  omega

theorem backward_loop_offset (n i j : Nat) (room : i < n) (slot : j < 6) :
    Schedule.moveWordOffset .backward n (6 + 6 * i + j) = 24 + 4 * j := by
  simp only [Schedule.moveWordOffset]
  rw [if_neg (by omega), if_pos (by omega)]
  congr 2
  omega

end Route7Move

#print axioms Route7Move.source_dest_distinct_of
#print axioms Route7Move.forward_future
#print axioms Route7Move.backward_future
#print axioms Route7Move.forward_loop_offset
#print axioms Route7Move.backward_loop_offset
