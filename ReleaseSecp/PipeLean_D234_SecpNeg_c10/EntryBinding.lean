import PipeLean_D234_SecpNeg_c10.Plan
import PipeLean_D234_SecpNeg_c10.ImageBinding
import TranslateSpan.SecpRawDeployment

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpNeg_c10.EntryBinding
open ArmCert.Translate.Model ArmCert.Translate.Model.StaticPie ArmCertWalk ArmBridge.Draft
open TranslateSpan TranslateSpan.SecpRawDeployment

def plan : Plan where
  code := Lean_D234_SecpNeg_c10E17.codeVAs
  accesses := [⟨0, 1, (0), false⟩, ⟨2, 1, (16), false⟩, ⟨14, 0, (0), true⟩, ⟨15, 0, (16), true⟩]
  regions := PipeLean_D234_SecpNeg_c10.rs_c00
  buffers := [(PipeLean_D234_SecpNeg_c10.O, 32), (PipeLean_D234_SecpNeg_c10.X, 32)]
  outputs := [(PipeLean_D234_SecpNeg_c10.O, 32)]
  normalize := id

theorem code_table : plan.code = [(5856, 2839547939), (5860, 2852388967), (5864, 2839615525), (5868, 2852454631), (5872, 2852520167), (5876, 3944677631), (5880, 3667854306), (5884, 3531635207), (5888, 2992636135), (5892, 2317811783), (5896, 3942842595), (5900, 4194566212), (5904, 4194631749), (5908, 3657826374), (5912, 2835353603), (5916, 2835421189), (5920, 3596551104)] := rfl

theorem site_table :
    plan.accesses.map (fun a => (a.index, Lean_D234_SecpNeg_c10Plan.Base.pin a.pin a.offset, 16, a.write)) =
      Lean_D234_SecpNeg_c10Plan.accesses_c00 := rfl

theorem region_table : plan.regions = PipeLean_D234_SecpNeg_c10.rs_c00 := rfl

theorem alias_table : plan.normalize = id := rfl

def entryCheck (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) : Bool :=
  check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

theorem entry_from_check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) :
    type_of% (of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry) :=
  of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

#print axioms entry_from_check
end PipeLean_D234_SecpNeg_c10.EntryBinding
