import PipeLean_D234_SecpSqr_c25.Plan
import PipeLean_D234_SecpSqr_c25.ImageBinding
import TranslateSpan.SecpRawDeployment

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSqr_c25.EntryBinding
open ArmCert.Translate.Model ArmCert.Translate.Model.StaticPie ArmCertWalk ArmBridge.Draft
open TranslateSpan TranslateSpan.SecpRawDeployment

def plan : Plan where
  code := Lean_D234_SecpSqr_c25E17.codeVAs
  accesses := [⟨0, 1, (0), false⟩, ⟨1, 1, (16), false⟩, ⟨133, 0, (0), true⟩, ⟨134, 0, (16), true⟩]
  regions := PipeLean_D234_SecpSqr_c25.rs_c00
  buffers := [(PipeLean_D234_SecpSqr_c25.O, 32), (PipeLean_D234_SecpSqr_c25.X, 32)]
  outputs := [(PipeLean_D234_SecpSqr_c25.O, 32)]
  normalize := PipeLean_D234_SecpSqr_c25.normalize_c00

theorem code_table : plan.code = [(7048, 2839555114), (7052, 2839622700), (7056, 2611641666), (7060, 3546348878), (7064, 2611903939), (7068, 2611903822), (7072, 2869855298), (7076, 3546283470), (7080, 2584608867), (7084, 2611707236), (7088, 3546348910), (7092, 2611903941), (7096, 2611903854), (7100, 2601221455), (7104, 2613804368), (7108, 2869855364), (7112, 3546283470), (7116, 2584608933), (7120, 2869887471), (7124, 3121611280), (7128, 2585723045), (7132, 2869887075), (7136, 3121610884), (7140, 2585723045), (7144, 2611772806), (7148, 3546348942), (7152, 2611903943), (7156, 2611903886), (7160, 2869855430), (7164, 3546283470), (7168, 2584608999), (7172, 2611838376), (7176, 3546348974), (7180, 2611903945), (7184, 2611903918), (7188, 2601352591), (7192, 2613935504), (7196, 2869855496), (7200, 3546283470), (7204, 2584609065), (7208, 2869887471), (7212, 3121611280), (7216, 2585723177), (7220, 2869887207), (7224, 3121611016), (7228, 2585723177), (7232, 3943432522), (7236, 4195156331), (7240, 3667862512), (7244, 3390046538), (7248, 3943694666), (7252, 3390046571), (7256, 3658482027), (7260, 2869166278), (7264, 3120890087), (7268, 3122594056), (7272, 2585723177), (7276, 2611641676), (7280, 3546348869), (7284, 2611313837), (7288, 2611313989), (7292, 2869265804), (7296, 3546283173), (7300, 2584019373), (7304, 2611707247), (7308, 3546348901), (7312, 2611313838), (7316, 2611314021), (7320, 2601221444), (7324, 2613804368), (7328, 2869265903), (7332, 3546283173), (7336, 2584019406), (7340, 2869166212), (7344, 3121611280), (7348, 2585723342), (7352, 2869166509), (7356, 3121611247), (7360, 2585723342), (7364, 2869297220), (7368, 3121021029), (7372, 3121086662), (7376, 3121152231), (7380, 3667862512), (7384, 3943432324), (7388, 4195156133), (7392, 4195287238), (7396, 4195221735), (7400, 3121611016), (7404, 2584740137), (7408, 3531635249), (7412, 2992636464), (7416, 2600893962), (7420, 2613476877), (7424, 2453699814), (7428, 3546348775), (7432, 2600893995), (7436, 2600933926), (7440, 2869330283), (7444, 3546348742), (7448, 2584084718), (7452, 2601025036), (7456, 2613607944), (7460, 2453699878), (7464, 3546348839), (7468, 2600893993), (7472, 2600933926), (7476, 2869330217), (7480, 3546348742), (7484, 2584084719), (7488, 2869559362), (7492, 3121283171), (7496, 3121348740), (7500, 3121152165), (7504, 2594125798), (7508, 2869756003), (7512, 3121479812), (7516, 3121086629), (7520, 2584674502), (7524, 2432697542), (7528, 2600893994), (7532, 3546348747), (7536, 2869330250), (7540, 2584413163), (7544, 2869559362), (7548, 3121283171), (7552, 3122593924), (7556, 3122593957), (7560, 2594124304), (7564, 3943694402), (7568, 4196335715), (7572, 4196335748), (7576, 3659464869), (7580, 2835352578), (7584, 2835420164), (7588, 3596551104)] := rfl

theorem site_table :
    plan.accesses.map (fun a => (a.index, Lean_D234_SecpSqr_c25Plan.Base.pin a.pin a.offset, 16, a.write)) =
      Lean_D234_SecpSqr_c25Plan.accesses_c00 := rfl

theorem region_table : plan.regions = PipeLean_D234_SecpSqr_c25.rs_c00 := rfl

theorem alias_table : plan.normalize = PipeLean_D234_SecpSqr_c25.normalize_c00 := rfl

def entryCheck (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) : Bool :=
  check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

theorem entry_from_check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) :
    type_of% (of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry) :=
  of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

#print axioms entry_from_check
end PipeLean_D234_SecpSqr_c25.EntryBinding
