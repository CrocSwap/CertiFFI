import ArmCertLoop.ContractDraft
import ArmCertLoop.NativeBytes
import LoopNative.Next
import LoopNative.Arithmetic
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv ArmBridge.CruxGenGuarded.ChainInvV2
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertLoop.CopyNative
open ContractDraft

/-- Internal collection of initial static deployment geometry. Public cards
retain the independently reviewed typed wrappers rather than this record. -/
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
  reserve : Nat := 0
  additionalSpans : List SpanMap.Span := []
  page : base.toNat % 4096 = 0
  low : base.toNat < 2 ^ 54
  returnLow : returnPC.toNat < 2 ^ 54
  sourceObject : SpanMap.NoWrap (sourceSpan s n)
  destObject : SpanMap.NoWrap (destSpan d n)
  disjoint : d.toNat + n ≤ s.toNat ∨ s.toNat + n ≤ d.toNat
  code : CodeGeometry mapping base
  codeWrite : CodeWriteSeparated mapping base d n
  data : DataGeometry mapping d s n (rowsFootprint spec.imageRows).byte
  injective : SpanMap.UnionInjective mapping (spans d s n)
  separated : ImageTableSeparated codeScope base mapping (rowsFootprint spec.imageRows).byte

def Context.budget (c : Context) : Nat := Schedule.copySteps c.n + c.reserve

def Context.footprints (c : Context) : List SpanMap.Span := spans c.d c.s c.n ++ c.additionalSpans

def Context.consumer (c : Context) :=
  SpanMap.consumerMap c.footprints (Image.codeVAs c.base Generated.imageStart Generated.imageWords)
    c.mapping (rowsFootprint c.spec.imageRows).byte


def Context.srcPA (c : Context) (i : Nat) : Nat := (c.mapping (c.s + BitVec.ofNat 64 i)).getD 0
def Context.dstPA (c : Context) (i : Nat) : Nat := (c.mapping (c.d + BitVec.ofNat 64 i)).getD 0

abbrev Env (c : Context) (k : Nat) (x : NativeState) : Prop :=
  ArmCertPipe.ChainInvG c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.base
    (offset c.base c.returnPC c.n) c.budget (fun _ _ => True) k x

structure Header (c : Context) (entry : NativeState) (i : Nat) (x : NativeState) : Prop where
  positive : 0 < c.n
  bound : i ≤ c.n
  environment : Env c (2 + 6 * i) x
  dest : x.regs.gpr[0] = c.d
  sourceCursor : x.regs.gpr[1] = c.s + BitVec.ofNat 64 i
  destCursor : x.regs.gpr[3] = c.d + BitVec.ofNat 64 i
  remaining : x.regs.gpr[2].toNat = c.n - i
  link : x.regs.gpr[30] = c.returnPC
  saved : ∀ r : Fin 31, 6 ≤ r.val → x.regs.gpr[r.val] = entry.regs.gpr[r.val]
  sp : x.regs.SP_EL0 = entry.regs.SP_EL0
  protectedRegs : NativeEntry.Effects.Frame {} entry.regs x.regs
  bytes : Bytes.CopyPrefix c.srcPA c.dstPA (Aux.memoryView entry) (Aux.memoryView x) c.n i

theorem source_mapped (c : Context) (i : Nat) (room : i < c.n) :
    ∃ pa : BitVec 56, c.mapping (c.s + BitVec.ofNat 64 i) = some pa.toNat ∧
      MemM1.MemReadIF.NotMMIO pa ∧ ¬ (rowsFootprint c.spec.imageRows).byte pa.toNat := by
  simpa only [sourceSpan, SpanMap.byteVA] using c.data (sourceSpan c.s c.n) (by simp [spans]) i room

theorem dest_mapped (c : Context) (i : Nat) (room : i < c.n) :
    ∃ pa : BitVec 56, c.mapping (c.d + BitVec.ofNat 64 i) = some pa.toNat ∧
      MemM1.MemReadIF.NotMMIO pa ∧ ¬ (rowsFootprint c.spec.imageRows).byte pa.toNat := by
  simpa only [destSpan, SpanMap.byteVA] using c.data (destSpan c.d c.n) (by simp [spans]) i room

theorem pc_body (c : Context) (i j : Nat) (room : i < c.n) (slot : j < 6)
    (x : NativeState) (env : Env c (2 + 6 * i + j) x) :
    x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memcpy_entry + 8 + 4 * j) := by
  have nz : c.n ≠ 0 := by omega
  have index : 2 + 6 * i + j ≠ Schedule.copySteps c.n := by simp only [Schedule.copySteps, if_neg nz]; omega
  rw [env.v2.v1.pc]
  simp only [offset, Schedule.nativeOffset, if_neg index, Schedule.copy_loop_offset c.n i j room slot]
  simp only [MemReloc.imageAddress, Nat.add_assoc]

/-- Bind one finite code word to the actual reached fetch, without any
future fetch or run-success premise. -/
def fetch_index (c : Context) (k index : Nat) (x : NativeState) (env : Env c k x)
    (room : index < Generated.imageWords.length)
    (pc : x.regs._PC = MemReloc.imageAddress c.base (Generated.imageStart + 4 * index)) :
    FetchObligations c.spec c.config c.rows c.mapping (Generated.imageWords.getD index 0) x :=
  Image.fetch_word c.spec c.config c.rows c.mapping c.footprints
    (rowsFootprint c.spec.imageRows).byte codeScope c.base Generated.imageStart Generated.imageWords
    (offset c.base c.returnPC c.n) c.budget k index room x env.v2 pc
    (fun byte bounded => by unfold codeScope; have := room; simp only [Generated.imageWords_length, Generated.imageStart] at *; omega)
    (c.code index room).1 (c.code index room).2 c.separated

#print axioms source_mapped
#print axioms dest_mapped
#print axioms pc_body
#print axioms fetch_index
end ArmCertLoop.CopyNative
