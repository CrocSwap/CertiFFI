-- Route 7 unit 3: the copy-chain environment over Runtime InvG (CurrentInv + MTE tag-status rows/trace).
import ArmCertLoop.CopyContext
import DefaultRuntimeCurrent
import DefaultRuntimeMemory
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false

namespace Route7Copy
open ArmCertLoop ArmCertLoop.CopyNative ArmCertLoop.ContractDraft

/-- `Image.fetch_word` over the MTE2-general CurrentInv (DefaultCurrent.fetchG in place of ArmCertPipe.fetchG). -/
def fetch_word_cur {domain : QueryDomain} (spec : TopologyImageSpec domain) (config : AttributeConfig)
    (rows : List PermissionRow) (mapping : BitVec 64 → Option Nat)
    (spans : List SpanMap.Span) (table scope : Nat → Prop)
    (base : BitVec 64) (start : Nat) (words : List (BitVec 32))
    (offset : Nat → BitVec 64) (budget k : Nat) (catalogue : NativeMteTagCheck.ControlCatalogue) (i : Nat) (room : i < words.length)
    (x : NativeState)
    (inv : ReleaseProfile.DefaultCurrent.CurrentInv spec config rows mapping
      (SpanMap.consumerMap spans (Image.codeVAs base start words) mapping table)
      scope (Image.wordImage start words) base base offset budget k catalogue x)
    (pc : x.regs._PC = MemReloc.imageAddress base (start + 4 * i))
    (inside : ∀ k, k < 4 → scope (start + 4 * i + k))
    (contiguous : ImageWordContiguous mapping base (start + 4 * i))
    (mmio : MappedNotMMIO mapping (MemReloc.imageAddress base (start + 4 * i)))
    (separated : ImageTableSeparated scope base mapping (rowsFootprint spec.imageRows).byte) :
    FetchObligations spec config rows mapping (words.getD i 0) x :=
  ReleaseProfile.DefaultCurrent.fetchG spec config rows mapping _ scope (Image.wordImage start words) base base offset
    budget k catalogue x inv (start + 4 * i) (words.getD i 0) pc inside contiguous mmio separated
    (Image.image_word start words i room)
    (fun acc shape => by
      rw [pc]
      exact SpanMap.fetch_permitted spans (Image.codeVAs base start words) mapping table _
        (Image.codeVA_member base start words i room) acc shape)

/-- Is step k a memory step (the LDRB at 2+6i or the STRB at 3+6i, i < n)? -/
def memStep (n k : Nat) : Bool := decide (2 ≤ k ∧ (k - 2) % 6 < 2 ∧ (k - 2) / 6 < n)

/-- Memory (LDRB/STRB) steps strictly before step k (each draws at most one MTE tag status). -/
def memPast (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => memPast n k + (if memStep n k then 1 else 0)

theorem memPast_succ (n k : Nat) : memPast n (k + 1) = memPast n k + (if memStep n k then 1 else 0) := rfl

/-- The copy environment: Runtime InvG over loops' Context, with tag-status capacity 2n. -/
abbrev EnvR (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k : Nat) (x : NativeState) : Prop :=
  ReleaseProfile.DefaultRuntime.InvG c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.base
    (offset c.base c.returnPC c.n) c.budget (fun _ _ => True) catalogue entry (2 * c.n) (memPast c.n) k x

theorem pc_body_r (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState)
    (i j : Nat) (room : i < c.n) (slot : j < 6)
    (x : NativeState) (env : EnvR c catalogue entry (2 + 6 * i + j) x) :
    x.regs._PC = MemReloc.imageAddress c.base (Generated.armcert_memcpy_entry + 8 + 4 * j) := by
  have nz : c.n ≠ 0 := by omega
  have index : 2 + 6 * i + j ≠ Schedule.copySteps c.n := by simp only [Schedule.copySteps, if_neg nz]; omega
  rw [env.core.v1.pc]
  simp only [offset, Schedule.nativeOffset, if_neg index, Schedule.copy_loop_offset c.n i j room slot]
  simp only [MemReloc.imageAddress, Nat.add_assoc]

def fetch_index_r (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k index : Nat)
    (x : NativeState) (env : EnvR c catalogue entry k x)
    (room : index < Generated.imageWords.length)
    (pc : x.regs._PC = MemReloc.imageAddress c.base (Generated.imageStart + 4 * index)) :
    FetchObligations c.spec c.config c.rows c.mapping (Generated.imageWords.getD index 0) x :=
  fetch_word_cur c.spec c.config c.rows c.mapping c.footprints
    (rowsFootprint c.spec.imageRows).byte codeScope c.base Generated.imageStart Generated.imageWords
    (offset c.base c.returnPC c.n) c.budget k catalogue index room x env.core pc
    (fun byte bounded => by unfold codeScope; have := room; simp only [Generated.imageWords_length, Generated.imageStart] at *; omega)
    (c.code index room).1 (c.code index room).2 c.separated

end Route7Copy

#print axioms Route7Copy.fetch_word_cur
#print axioms Route7Copy.memPast_succ
#print axioms Route7Copy.pc_body_r
#print axioms Route7Copy.fetch_index_r
