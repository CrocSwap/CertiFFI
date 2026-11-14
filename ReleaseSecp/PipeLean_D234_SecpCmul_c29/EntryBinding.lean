import PipeLean_D234_SecpCmul_c29.Plan
import PipeLean_D234_SecpCmul_c29.ImageBinding
import TranslateSpan.SecpRawDeployment

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpCmul_c29.EntryBinding
open ArmCert.Translate.Model ArmCert.Translate.Model.StaticPie ArmCertWalk ArmBridge.Draft
open TranslateSpan TranslateSpan.SecpRawDeployment

def plan : Plan where
  code := Lean_D234_SecpCmul_c29E17.codeVAs
  accesses := [⟨0, 2, (0), false⟩, ⟨1, 2, (16), false⟩, ⟨28, 0, (0), true⟩, ⟨29, 0, (16), true⟩]
  regions := PipeLean_D234_SecpCmul_c29.rs_c00
  buffers := [(PipeLean_D234_SecpCmul_c29.O, 32), (PipeLean_D234_SecpCmul_c29.X, 32)]
  outputs := [(PipeLean_D234_SecpCmul_c29.O, 32)]
  normalize := PipeLean_D234_SecpCmul_c29.normalize_c00

theorem code_table : plan.code = [(7908, 2839552071), (7912, 2839619657), (7916, 2600959011), (7920, 2601024548), (7924, 2601090085), (7928, 2601155622), (7932, 2613541927), (7936, 2613607464), (7940, 2613673001), (7944, 2613738538), (7948, 2869362820), (7952, 3121086629), (7956, 3121152198), (7960, 3122594122), (7964, 2432697674), (7968, 3531635241), (7972, 2992636201), (7976, 2601090375), (7980, 2613673288), (7984, 2869362787), (7988, 3121086596), (7992, 3122593957), (7996, 3122593990), (8000, 2594124073), (8004, 3943235683), (8008, 4196335748), (8012, 4196335781), (8016, 3659464902), (8020, 2835353603), (8024, 2835421189), (8028, 3596551104)] := rfl

theorem site_table :
    plan.accesses.map (fun a => (a.index, Lean_D234_SecpCmul_c29Plan.Base.pin a.pin a.offset, 16, a.write)) =
      Lean_D234_SecpCmul_c29Plan.accesses_c00 := rfl

theorem region_table : plan.regions = PipeLean_D234_SecpCmul_c29.rs_c00 := rfl

theorem alias_table : plan.normalize = PipeLean_D234_SecpCmul_c29.normalize_c00 := rfl

def entryCheck (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) : Bool :=
  check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

theorem entry_from_check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) :
    type_of% (of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry) :=
  of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

#print axioms entry_from_check
end PipeLean_D234_SecpCmul_c29.EntryBinding
