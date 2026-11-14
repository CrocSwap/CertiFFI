import ReleaseProfile.GB10.ModelEntry
import ReleaseProfile.GB10.SpecWitness
import ReleaseProfile.GB10.TablesBuilder
import ReleaseProfile.RuntimeGB10.WorldPlan
import ReleaseProfile.RuntimeGB10.WorldCases
import SparseELF.R14
import PipeR14.FetchR14

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

/-!
# Runtime positive-C2 world

`RuntimeWorld` holds the closed program/memory/caller data of a Runtime model entry: one RAM plan (code ++ tables ++
data, distinct addresses), program data and the entry `DataPart` (GPRs, SP, PC, page-table roots). Nothing here is
configuration: registers other than `DataPart` are the canonical source (`makeModelEntry`). Permission rows remain a
parameter (they are checked under the SourceSpec controls via `images_of_checks`).
-/

namespace ReleaseProfile.GB10.Runtime

open ReleaseProfile.MachineSource ReleaseProfile.GB10

structure RuntimeWorld where
  plan : List (Nat × BitVec 8)
  planKeys : plan.Pairwise (fun a b => (a.1 == b.1) = false)
  rows : List ArmCert.Translate.Model.PermissionRow
  mapping : BitVec 64 → Option Nat
  table : Nat → Prop
  sc : Nat → Prop
  bytes : Array Nat
  base : BitVec 64
  ifunc : Nat → MemReloc.Word
  p : R14E17.Pins
  budget : Nat
  inputs : List (BitVec 64)
  data : DataPart

def RuntimeWorld.payload (w : RuntimeWorld) (pcount : BitVec 88) : ModelPayload :=
  ⟨{ w.data with PhysicalCount := pcount }, Std.ExtHashMap.ofList w.plan⟩

def RuntimeWorld.entry (sem : ModelSemantics) (rho : AdmissibleSourceCompletion) (caller : AdmissibleCaller rho)
    (w : RuntimeWorld) (pcount : BitVec 88) : ArmBridge.Draft.NativeState :=
  makeModelEntry sem rho caller (w.payload pcount)

theorem RuntimeWorld.realizes (sem : ModelSemantics) (rho : AdmissibleSourceCompletion)
    (caller : AdmissibleCaller rho) (w : RuntimeWorld) (pcount : BitVec 88) :
    ∀ ab ∈ w.plan, (w.entry sem rho caller pcount).mem[ab.1]? = some ab.2 :=
  fun ⟨_, _⟩ mem => Std.ExtHashMap.getElem?_ofList_of_mem (BEq.refl _) w.planKeys mem

/-! ## Shared Runtime world instances (program data only) -/

namespace World

open ReleaseProfile.RuntimeGB10

def layout : S1LogicalReference.Layout := ⟨0, 48, ReleaseProfile.RuntimeGB10.World.root⟩

theorem queries_ok : ReleaseProfile.RuntimeGB10.World.queries.all
    (ArmCertWalk.checkSpecQuery gb10Physical layout ReleaseProfile.RuntimeGB10.World.logicalRows
      ReleaseProfile.RuntimeGB10.World.imageRows 4) = true := by decide

/-- Tables-only topology data (no params/controls), page-keyed. -/
noncomputable def tables : TopologyTables (fun q => ∃ q0 ∈ ReleaseProfile.RuntimeGB10.World.queries,
    ArmCertWalk.SamePage q0.va q.va) :=
  TablesBuilder.tablesOfChecksPage layout ReleaseProfile.RuntimeGB10.World.logicalRows
    ReleaseProfile.RuntimeGB10.World.imageRows ReleaseProfile.RuntimeGB10.World.queries 4
    ReleaseProfile.RuntimeGB10.World.spec_rows queries_ok

/-- Oracle draws (semantics choices, not configuration): all zero, as the Heap world. -/
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

/-- Entry data of a case: its entry GPRs, SP_EL0 = 0x200000, PC = image base + entry, page-table roots
TTBR0_EL2 = HTTBR = 0x80000000, TTBR1_EL2 = 0. -/
def entryData (gprs : Vector (BitVec 64) 31) (entry : Nat) : DataPart where
  gpr := gprs
  SP_EL3 := 0#64
  SP_EL2 := 0#64
  SP_EL1 := 0#64
  SP_EL0 := 0x200000#64
  _ZT0 := 0#512
  _ZA := Vector.replicate 256 0#2048
  _FFR := 0#256
  _P := Vector.replicate 16 0#256
  _Z := Vector.replicate 32 0#2048
  PhysicalCount := 0#88
  _PC := 0x400000#64 + BitVec.ofNat 64 entry
  TTBR0_EL2 := 0x80000000#128
  TTBR1_EL2 := 0#128
  HTTBR := 0x80000000#64
  timers := fun _ => 0#64

theorem planKeys (db : Nat → BitVec 8) :
    (WorldPlan.plan db).Pairwise (fun a b => (a.1 == b.1) = false) := by
  have h := List.pairwise_map.1 (List.nodup_iff_pairwise_ne.1 (WorldPlan.plan_nodup db))
  exact h.imp fun {a b} ne => by simpa [beq_eq_false_iff_ne] using ne

end World

end ReleaseProfile.GB10.Runtime

#print axioms ReleaseProfile.GB10.Runtime.RuntimeWorld.realizes
#print axioms ReleaseProfile.GB10.Runtime.World.planKeys
