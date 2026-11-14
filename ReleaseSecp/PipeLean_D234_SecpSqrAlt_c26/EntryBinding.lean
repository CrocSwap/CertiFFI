import PipeLean_D234_SecpSqrAlt_c26.Plan
import PipeLean_D234_SecpSqrAlt_c26.ImageBinding
import TranslateSpan.SecpRawDeployment

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSqrAlt_c26.EntryBinding
open ArmCert.Translate.Model ArmCert.Translate.Model.StaticPie ArmCertWalk ArmBridge.Draft
open TranslateSpan TranslateSpan.SecpRawDeployment

def plan : Plan where
  code := Lean_D234_SecpSqrAlt_c26E17.codeVAs
  accesses := [⟨0, 1, (0), false⟩, ⟨3, 1, (16), false⟩, ⟨76, 0, (0), true⟩, ⟨77, 0, (16), true⟩]
  regions := PipeLean_D234_SecpSqrAlt_c26.rs_c00
  buffers := [(PipeLean_D234_SecpSqrAlt_c26.O, 32), (PipeLean_D234_SecpSqrAlt_c26.X, 32)]
  outputs := [(PipeLean_D234_SecpSqrAlt_c26.O, 32)]
  normalize := id

theorem code_table : plan.code = [(7592, 2839546914), (7596, 2600696905), (7600, 2613279818), (7604, 2839614500), (7608, 2600827979), (7612, 2613410892), (7616, 2600762439), (7620, 2613345350), (7624, 2869363018), (7628, 3120955755), (7632, 2600762471), (7636, 2613345382), (7640, 2585723078), (7644, 2869363051), (7648, 2600828045), (7652, 2613410958), (7656, 3120955788), (7660, 2600828007), (7664, 2613410918), (7668, 2585723078), (7672, 2869363084), (7676, 3120955821), (7680, 2585723342), (7684, 2869494057), (7688, 3121217866), (7692, 3121283435), (7696, 3121349004), (7700, 3121414573), (7704, 3121480142), (7708, 2594125798), (7712, 2613214279), (7716, 2600631368), (7720, 2869362985), (7724, 2600696935), (7728, 3121021258), (7732, 2613279847), (7736, 3121021291), (7740, 2600762503), (7744, 3121021324), (7748, 2613345415), (7752, 3121021357), (7756, 2600828071), (7760, 3121021390), (7764, 2613410983), (7768, 2584150214), (7772, 3531635235), (7776, 2992636003), (7780, 2601286759), (7784, 2613869668), (7788, 2869362952), (7792, 2601352295), (7796, 2613935213), (7800, 3121021225), (7804, 2601417831), (7808, 2614000750), (7812, 3121021258), (7816, 2600893543), (7820, 2613476454), (7824, 3121021291), (7828, 2594125804), (7832, 2869166377), (7836, 3121414474), (7840, 3121480043), (7844, 2584084876), (7848, 2432697730), (7852, 2600631399), (7856, 2613214310), (7860, 2869362952), (7864, 3120955689), (7868, 3122594122), (7872, 3122594155), (7876, 2594123875), (7880, 3942842632), (7884, 4196335913), (7888, 4196335946), (7892, 3659465067), (7896, 2835358728), (7900, 2835426314), (7904, 3596551104)] := rfl

theorem site_table :
    plan.accesses.map (fun a => (a.index, Lean_D234_SecpSqrAlt_c26Plan.Base.pin a.pin a.offset, 16, a.write)) =
      Lean_D234_SecpSqrAlt_c26Plan.accesses_c00 := rfl

theorem region_table : plan.regions = PipeLean_D234_SecpSqrAlt_c26.rs_c00 := rfl

theorem alias_table : plan.normalize = id := rfl

def entryCheck (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) : Bool :=
  check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

theorem entry_from_check (raw : CheckedTopology.Raw) (config : AttributeConfig) (rows : List PermissionRow)
    (mapping : BitVec 64 → Option Nat) (base : BitVec 64) (entry : NativeState) :
    type_of% (of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry) :=
  of_check plan (referenceImageI SecpArtifact.elf base (fun _ => 0)) raw config rows mapping base entry

#print axioms entry_from_check
end PipeLean_D234_SecpSqrAlt_c26.EntryBinding
