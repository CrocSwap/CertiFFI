import PipeLean_D234_SecpMulAlt_c19.Plan
import PipeLean_D234_SecpMulAlt_c19.ImageBinding
import TranslateSpan.SecpRawDeployment

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpMulAlt_c19.EntryBinding
open ArmCert.Translate.Model ArmCert.Translate.Model.StaticPie ArmCertWalk ArmBridge.Draft
open TranslateSpan TranslateSpan.SecpRawDeployment

def plan : Plan where
  code := Lean_D234_SecpMulAlt_c19E17.codeVAs
  accesses := [⟨0, 1, (0), false⟩, ⟨1, 2, (0), false⟩, ⟨7, 2, (16), false⟩, ⟨15, 1, (16), false⟩, ⟨98, 0, (0), true⟩, ⟨99, 0, (16), true⟩]
  regions := PipeLean_D234_SecpMulAlt_c19.rs_c00
  buffers := [(PipeLean_D234_SecpMulAlt_c19.O, 32), (PipeLean_D234_SecpMulAlt_c19.X, 32), (PipeLean_D234_SecpMulAlt_c19.Y, 32)]
  outputs := [(PipeLean_D234_SecpMulAlt_c19.O, 32)]
  normalize := id

theorem code_table : plan.code = [(6644, 2839547939), (6648, 2839552071), (6652, 2600959084), (6656, 2613541997), (6660, 2601024619), (6664, 2613607534), (6668, 2869625261), (6672, 2839619657), (6676, 2601090155), (6680, 2613673071), (6684, 3121283534), (6688, 2601155691), (6692, 2613738608), (6696, 3121283567), (6700, 2585723408), (6704, 2839615525), (6708, 2600959115), (6712, 2869625261), (6716, 2601024651), (6720, 3121283534), (6724, 2601090187), (6728, 3121283567), (6732, 2601155723), (6736, 3121283600), (6740, 2613738627), (6744, 2585722979), (6748, 2613542027), (6752, 2869625294), (6756, 2613607563), (6760, 3121283567), (6764, 2613673099), (6768, 3121283600), (6772, 2585722979), (6776, 2600959147), (6780, 2869625294), (6784, 2601024683), (6788, 3121283567), (6792, 2601090219), (6796, 3121283600), (6800, 2601155755), (6804, 3121283171), (6808, 2613738660), (6812, 2585723012), (6816, 2613542059), (6820, 2869625327), (6824, 2613607595), (6828, 3121283600), (6832, 2613673131), (6836, 3121283171), (6840, 2585723012), (6844, 2600959179), (6848, 2869625327), (6852, 2601024715), (6856, 3121283600), (6860, 2601090251), (6864, 3121283171), (6868, 2601155787), (6872, 3121283204), (6876, 2613738693), (6880, 2585723045), (6884, 2613542091), (6888, 2869625360), (6892, 2613607627), (6896, 3121283171), (6900, 2613673163), (6904, 3121283204), (6908, 2585723045), (6912, 3531635239), (6916, 2992636135), (6920, 2601549035), (6924, 2614131945), (6928, 2869625228), (6932, 2600697067), (6936, 2613279971), (6940, 3121283501), (6944, 2600762603), (6948, 2613345508), (6952, 3121283534), (6956, 2600828139), (6960, 2613411045), (6964, 3121283567), (6968, 2594125808), (6972, 2869494189), (6976, 3120759246), (6980, 3120824815), (6984, 2584019472), (6988, 2432697864), (6992, 2601024747), (6996, 2613607657), (7000, 2869625228), (7004, 3121152429), (7008, 3122594254), (7012, 3122594287), (7016, 2594124007), (7020, 3943104908), (7024, 4196336045), (7028, 4196336078), (7032, 3659465199), (7036, 2835362828), (7040, 2835430414), (7044, 3596551104)] := rfl

theorem site_table :
    plan.accesses.map (fun a => (a.index, Lean_D234_SecpMulAlt_c19Plan.Base.pin a.pin a.offset, 16, a.write)) =
      Lean_D234_SecpMulAlt_c19Plan.accesses_c00 := rfl

theorem region_table : plan.regions = PipeLean_D234_SecpMulAlt_c19.rs_c00 := rfl

theorem alias_table : plan.normalize = id := rfl

def entryCheck (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) : Bool :=
  check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

theorem entry_from_check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) :
    type_of% (of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry) :=
  of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

#print axioms entry_from_check
end PipeLean_D234_SecpMulAlt_c19.EntryBinding
