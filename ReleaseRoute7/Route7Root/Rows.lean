-- Route 7 / memcpy roots, part 1 (loops): the card v2 caller / loader / E34 rows as typed claim inputs, the copy
-- Context built from them, and the complete memcpy (run + CopyPost + fetched-PC coverage) from EnvR at the actual
-- entry plus those rows. Part 2 (C1 root) composes this with generic Route7Entry.invG_at_entry.
import Route7Copy.Run
import CertiFFIClaim.Kinds
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false

namespace Route7Root
open ArmCertLoop ArmCertLoop.CopyNative ArmCertLoop.ContractDraft Route7Copy CertiFFI.Claim

/-- Card v2 rows (caller contracts, loader / deployment obligations and E34), each a registered claim input.
Grades come from the registry: caller_contract, loader_image_obligation, DeploymentObligation "E34". -/
structure MemcpyRows {domain : QueryDomain} (spec : TopologyImageSpec domain) (mapping : BitVec 64 → Option Nat)
    (base d s returnPC : BitVec 64) (n : Nat) (e : NativeState) : Prop where
  page : DeploymentObligation "loop:load-base-page" (base.toNat % 4096 = 0)
  low : DeploymentObligation "loop:load-base-low" (base.toNat < 2 ^ 54)
  returnLow : CallerContract "loop:return-canonical" (returnPC.toNat < 2 ^ 54)
  sourceObject : CallerContract "loop:memcpy:source-object" (SpanMap.NoWrap (sourceSpan s n))
  destObject : CallerContract "loop:memcpy:destination-object" (SpanMap.NoWrap (destSpan d n))
  disjoint : CallerContract "loop:memcpy:disjoint" (d.toNat + n ≤ s.toNat ∨ s.toNat + n ≤ d.toNat)
  code : DeploymentObligation "loop:code-geometry" (CodeGeometry mapping base)
  codeWrite : DeploymentObligation "loop:code-write-separated" (CodeWriteSeparated mapping base d n)
  data : DeploymentObligation "loop:data-geometry" (DataGeometry mapping d s n (rowsFootprint spec.imageRows).byte)
  injective : DeploymentObligation "loop:union-injective" (SpanMap.UnionInjective mapping (spans d s n))
  separated : DeploymentObligation "loop:image-table-separated"
    (ImageTableSeparated codeScope base mapping (rowsFootprint spec.imageRows).byte)
  args : CallerContract "loop:memcpy:args" (Args d s returnPC n e)
  present : CallerContract "loop:memcpy:source-present" (SourcePresent mapping s n e)
  nodup : DeploymentObligation "E34" ((spec.logicalRows.map (·.logical)).Nodup)

/-- The copy Context determined by the root's data and rows (config and rows are the canonical source's). -/
def MemcpyRows.context {domain : QueryDomain} {spec : TopologyImageSpec domain} {mapping : BitVec 64 → Option Nat}
    {base d s returnPC : BitVec 64} {n : Nat} {e : NativeState}
    (r : MemcpyRows spec mapping base d s returnPC n e) (config : AttributeConfig) (rows : List PermissionRow) :
    Context where
  domain := domain
  spec := spec
  config := config
  rows := rows
  mapping := mapping
  base := base
  d := d
  s := s
  returnPC := returnPC
  n := n
  page := r.page.holds
  low := r.low.holds
  returnLow := r.returnLow.holds
  sourceObject := r.sourceObject.holds
  destObject := r.destObject.holds
  disjoint := r.disjoint.holds
  code := r.code.holds
  codeWrite := r.codeWrite.holds
  data := r.data.holds
  injective := r.injective.holds
  separated := r.separated.holds

/-- Complete memcpy from EnvR at the actual entry plus the card rows: the exact copySteps n run succeeds, ends in
CopyPost, and every state it passes through is at a reviewed memcpy word or (after RET) at returnPC. -/
theorem memcpy_of_env (real : Type) [Sail.SailReal real] {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {mapping : BitVec 64 → Option Nat} {base d s returnPC : BitVec 64} {n : Nat} {e : NativeState}
    (r : MemcpyRows spec mapping base d s returnPC n e) (config : AttributeConfig) (rows : List PermissionRow)
    (catalogue : NativeMteTagCheck.ControlCatalogue) (env : EnvR (r.context config rows) catalogue e 0 e) :
    ∃ fin, Uget.Chain.modelRun real (Schedule.copySteps n) e = .ok () fin ∧
      CopyPost mapping d s returnPC n e fin ∧ Covered real (PcOk (r.context config rows)) (Schedule.copySteps n) e ∧
      Route7Trace.Traced real spec mapping (recsOf (r.context config rows)) (pcOf (r.context config rows))
        (Schedule.copySteps n) 0 e :=
  run_r real (r.context config rows) catalogue r.nodup.holds e r.args.holds r.present.holds env

end Route7Root
#print axioms Route7Root.memcpy_of_env
