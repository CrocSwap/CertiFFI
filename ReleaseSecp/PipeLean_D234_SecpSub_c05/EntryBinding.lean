import PipeLean_D234_SecpSub_c05.Plan
import PipeLean_D234_SecpSub_c05.ImageBinding
import TranslateSpan.SecpRawDeployment

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSub_c05.EntryBinding
open ArmCert.Translate.Model ArmCert.Translate.Model.StaticPie ArmCertWalk ArmBridge.Draft
open TranslateSpan TranslateSpan.SecpRawDeployment

def plan : Plan where
  code := Lean_D234_SecpSub_c05E17.codeVAs
  accesses := [⟨0, 1, (0), false⟩, ⟨1, 2, (0), false⟩, ⟨4, 1, (16), false⟩, ⟨5, 2, (16), false⟩, ⟨15, 0, (0), true⟩, ⟨16, 0, (16), true⟩]
  regions := PipeLean_D234_SecpSub_c05.rs_c05
  buffers := [(PipeLean_D234_SecpSub_c05.O, 32), (PipeLean_D234_SecpSub_c05.X, 32), (PipeLean_D234_SecpSub_c05.Y, 32)]
  outputs := [(PipeLean_D234_SecpSub_c05.O, 32)]
  normalize := PipeLean_D234_SecpSub_c05.normalize_c05

theorem code_table : plan.code = [(5784, 2839549989), (5788, 2839546948), (5792, 3942908069), (5796, 4194500806), (5800, 2839617575), (5804, 2839612484), (5808, 4194566375), (5812, 4194500872), (5816, 3531635236), (5820, 2992636035), (5824, 2594123875), (5828, 3942842533), (5832, 4196335814), (5836, 4196335847), (5840, 3659464968), (5844, 2835355653), (5848, 2835423239), (5852, 3596551104)] := rfl

theorem site_table :
    plan.accesses.map (fun a => (a.index, Lean_D234_SecpSub_c05Plan.Base.pin a.pin a.offset, 16, a.write)) =
      Lean_D234_SecpSub_c05Plan.accesses_c05 := rfl

theorem region_table : plan.regions = PipeLean_D234_SecpSub_c05.rs_c05 := rfl

theorem alias_table : plan.normalize = PipeLean_D234_SecpSub_c05.normalize_c05 := rfl

def entryCheck (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) : Bool :=
  check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

theorem entry_from_check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) :
    type_of% (of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry) :=
  of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

#print axioms entry_from_check
end PipeLean_D234_SecpSub_c05.EntryBinding
