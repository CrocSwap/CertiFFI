import PipeLean_D234_SecpDouble_c13.Plan
import PipeLean_D234_SecpDouble_c13.ImageBinding
import TranslateSpan.SecpRawDeployment

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpDouble_c13.EntryBinding
open ArmCert.Translate.Model ArmCert.Translate.Model.StaticPie ArmCertWalk ArmBridge.Draft
open TranslateSpan TranslateSpan.SecpRawDeployment

def plan : Plan where
  code := Lean_D234_SecpDouble_c13E17.codeVAs
  accesses := [⟨0, 1, (16), false⟩, ⟨3, 1, (0), false⟩, ⟨19, 0, (0), true⟩, ⟨20, 0, (16), true⟩]
  regions := PipeLean_D234_SecpDouble_c13.rs_c00
  buffers := [(PipeLean_D234_SecpDouble_c13.O, 32), (PipeLean_D234_SecpDouble_c13.X, 32)]
  outputs := [(PipeLean_D234_SecpDouble_c13.O, 32)]
  normalize := PipeLean_D234_SecpDouble_c13.normalize_c00

theorem code_table : plan.code = [(5924, 2839614500), (5928, 3548380326), (5932, 2479160485), (5936, 2839546914), (5940, 2479094916), (5944, 2315583623), (5948, 2479029347), (5952, 2315452647), (5956, 3548379202), (5960, 3531635240), (5964, 2992636168), (5968, 2869428319), (5972, 3122594047), (5976, 3122593990), (5980, 2594115848), (5984, 2869428290), (5988, 3122593891), (5992, 3122593924), (5996, 2585723045), (6000, 2835352578), (6004, 2835420164), (6008, 3596551104)] := rfl

theorem site_table :
    plan.accesses.map (fun a => (a.index, Lean_D234_SecpDouble_c13Plan.Base.pin a.pin a.offset, 16, a.write)) =
      Lean_D234_SecpDouble_c13Plan.accesses_c00 := rfl

theorem region_table : plan.regions = PipeLean_D234_SecpDouble_c13.rs_c00 := rfl

theorem alias_table : plan.normalize = PipeLean_D234_SecpDouble_c13.normalize_c00 := rfl

def entryCheck (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) : Bool :=
  check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

theorem entry_from_check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) :
    type_of% (of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry) :=
  of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

#print axioms entry_from_check
end PipeLean_D234_SecpDouble_c13.EntryBinding
