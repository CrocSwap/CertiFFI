import PipeLean_D234_SecpMod4_c30.Plan
import PipeLean_D234_SecpMod4_c30.ImageBinding
import TranslateSpan.SecpRawDeployment

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpMod4_c30.EntryBinding
open ArmCert.Translate.Model ArmCert.Translate.Model.StaticPie ArmCertWalk ArmBridge.Draft
open TranslateSpan TranslateSpan.SecpRawDeployment

def plan : Plan where
  code := Lean_D234_SecpMod4_c30E17.codeVAs
  accesses := [⟨0, 1, (0), false⟩, ⟨1, 1, (16), false⟩, ⟨12, 0, (0), true⟩, ⟨13, 0, (16), true⟩]
  regions := PipeLean_D234_SecpMod4_c30.rs_c00
  buffers := [(PipeLean_D234_SecpMod4_c30.O, 32), (PipeLean_D234_SecpMod4_c30.X, 32)]
  outputs := [(PipeLean_D234_SecpMod4_c30.O, 32)]
  normalize := id

theorem code_table : plan.code = [(8032, 2839546914), (8036, 2839614500), (8040, 2315518054), (8044, 2315583686), (8048, 3531635239), (8052, 2992636135), (8056, 2869035239), (8060, 3122593990), (8064, 2592550978), (8068, 2592485475), (8072, 2592485508), (8076, 2592485541), (8080, 2835352578), (8084, 2835420164), (8088, 3596551104)] := rfl

theorem site_table :
    plan.accesses.map (fun a => (a.index, Lean_D234_SecpMod4_c30Plan.Base.pin a.pin a.offset, 16, a.write)) =
      Lean_D234_SecpMod4_c30Plan.accesses_c00 := rfl

theorem region_table : plan.regions = PipeLean_D234_SecpMod4_c30.rs_c00 := rfl

theorem alias_table : plan.normalize = id := rfl

def entryCheck (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) : Bool :=
  check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

theorem entry_from_check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) :
    type_of% (of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry) :=
  of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

#print axioms entry_from_check
end PipeLean_D234_SecpMod4_c30.EntryBinding
