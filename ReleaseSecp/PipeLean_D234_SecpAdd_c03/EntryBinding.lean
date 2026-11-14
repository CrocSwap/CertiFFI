import PipeLean_D234_SecpAdd_c03.Plan
import PipeLean_D234_SecpAdd_c03.ImageBinding
import TranslateSpan.SecpRawDeployment

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpAdd_c03.EntryBinding
open ArmCert.Translate.Model ArmCert.Translate.Model.StaticPie ArmCertWalk ArmBridge.Draft
open TranslateSpan TranslateSpan.SecpRawDeployment

def plan : Plan where
  code := Lean_D234_SecpAdd_c03E17.codeVAs
  accesses := [⟨0, 1, (0), false⟩, ⟨1, 2, (0), false⟩, ⟨4, 1, (16), false⟩, ⟨5, 2, (16), false⟩, ⟨21, 0, (0), true⟩, ⟨22, 0, (16), true⟩]
  regions := PipeLean_D234_SecpAdd_c03.rs_c00
  buffers := [(PipeLean_D234_SecpAdd_c03.O, 32), (PipeLean_D234_SecpAdd_c03.X, 32), (PipeLean_D234_SecpAdd_c03.Y, 32)]
  outputs := [(PipeLean_D234_SecpAdd_c03.O, 32)]
  normalize := PipeLean_D234_SecpAdd_c03.normalize_c00

theorem code_table : plan.code = [(5688, 2839549989), (5692, 2839546948), (5696, 2869166245), (5700, 3120758982), (5704, 2839617575), (5708, 2839612484), (5712, 3120824551), (5716, 2315714761), (5720, 3120759048), (5724, 2315780393), (5728, 2585723875), (5732, 3531635236), (5736, 2992636036), (5740, 2869166271), (5744, 3122594111), (5748, 3122593891), (5752, 2594115716), (5756, 2869166245), (5760, 3122593990), (5764, 3122594023), (5768, 2585723144), (5772, 2835355653), (5776, 2835423239), (5780, 3596551104)] := rfl

theorem site_table :
    plan.accesses.map (fun a => (a.index, Lean_D234_SecpAdd_c03Plan.Base.pin a.pin a.offset, 16, a.write)) =
      Lean_D234_SecpAdd_c03Plan.accesses_c00 := rfl

theorem region_table : plan.regions = PipeLean_D234_SecpAdd_c03.rs_c00 := rfl

theorem alias_table : plan.normalize = PipeLean_D234_SecpAdd_c03.normalize_c00 := rfl

def entryCheck (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) : Bool :=
  check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

theorem entry_from_check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) :
    type_of% (of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry) :=
  of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

#print axioms entry_from_check
end PipeLean_D234_SecpAdd_c03.EntryBinding
