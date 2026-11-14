import Lean_D234_SecpSqrAlt_c27E17.Fetch
import SecpArtifact.Elf
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSqrAlt_c27.ImageBinding
open ArmCert.Translate.Model.StaticPie

theorem image_binds : Binds SecpArtifact.elf Lean_D234_SecpSqrAlt_c27Scoped.slices := SecpArtifact.sub_binds
theorem scoped_image : ScopedAdmitted SecpArtifact.elf Lean_D234_SecpSqrAlt_c27Scoped.closure Lean_D234_SecpSqrAlt_c27Scoped.slices.rela :=
  Lean_D234_SecpSqrAlt_c27Scoped.lean_d234_secpsqralt_c27_scoped _ image_binds

private def words : List (Nat × Nat) := [(7592, 2839546914), (7596, 2600696905), (7600, 2613279818), (7604, 2839614500), (7608, 2600827979), (7612, 2613410892), (7616, 2600762439), (7620, 2613345350), (7624, 2869363018), (7628, 3120955755), (7632, 2600762471), (7636, 2613345382), (7640, 2585723078), (7644, 2869363051), (7648, 2600828045), (7652, 2613410958), (7656, 3120955788), (7660, 2600828007), (7664, 2613410918), (7668, 2585723078), (7672, 2869363084), (7676, 3120955821), (7680, 2585723342), (7684, 2869494057), (7688, 3121217866), (7692, 3121283435), (7696, 3121349004), (7700, 3121414573), (7704, 3121480142), (7708, 2594125798), (7712, 2613214279), (7716, 2600631368), (7720, 2869362985), (7724, 2600696935), (7728, 3121021258), (7732, 2613279847), (7736, 3121021291), (7740, 2600762503), (7744, 3121021324), (7748, 2613345415), (7752, 3121021357), (7756, 2600828071), (7760, 3121021390), (7764, 2613410983), (7768, 2584150214), (7772, 3531635235), (7776, 2992636003), (7780, 2601286759), (7784, 2613869668), (7788, 2869362952), (7792, 2601352295), (7796, 2613935213), (7800, 3121021225), (7804, 2601417831), (7808, 2614000750), (7812, 3121021258), (7816, 2600893543), (7820, 2613476454), (7824, 3121021291), (7828, 2594125804), (7832, 2869166377), (7836, 3121414474), (7840, 3121480043), (7844, 2584084876), (7848, 2432697730), (7852, 2600631399), (7856, 2613214310), (7860, 2869362952), (7864, 3120955689), (7868, 3122594122), (7872, 3122594155), (7876, 2594123875), (7880, 3942842632), (7884, 4196335913), (7888, 4196335946), (7892, 3659465067), (7896, 2835358728), (7900, 2835426314), (7904, 3596551104)]
private theorem words_match : Lean_D234_SecpSqrAlt_c27E17.codeVAs = words := by rfl

private def fileBytes : List Nat := [34, 12, 64, 169, 73, 124, 3, 155, 74, 124, 195, 155, 36, 20, 65, 169, 75, 124, 5, 155, 76, 124, 197, 155, 71, 124, 4, 155, 70, 124, 196, 155, 74, 1, 7, 171, 107, 1, 6, 186, 103, 124, 4, 155, 102, 124, 196, 155, 198, 0, 31, 154, 107, 1, 7, 171, 141, 124, 5, 155, 142, 124, 197, 155, 140, 1, 6, 186, 103, 124, 5, 155, 102, 124, 197, 155, 198, 0, 31, 154, 140, 1, 7, 171, 173, 1, 6, 186, 206, 1, 31, 154, 41, 1, 9, 171, 74, 1, 10, 186, 107, 1, 11, 186, 140, 1, 12, 186, 173, 1, 13, 186, 206, 1, 14, 186, 230, 55, 159, 154, 71, 124, 194, 155, 72, 124, 2, 155, 41, 1, 7, 171, 103, 124, 3, 155, 74, 1, 7, 186, 103, 124, 195, 155, 107, 1, 7, 186, 135, 124, 4, 155, 140, 1, 7, 186, 135, 124, 196, 155, 173, 1, 7, 186, 167, 124, 5, 155, 206, 1, 7, 186, 167, 124, 197, 155, 198, 0, 7, 154, 35, 122, 128, 210, 99, 0, 96, 178, 103, 124, 12, 155, 100, 124, 204, 155, 8, 1, 7, 171, 103, 124, 13, 155, 109, 124, 205, 155, 41, 1, 7, 186, 103, 124, 14, 155, 110, 124, 206, 155, 74, 1, 7, 186, 103, 124, 6, 155, 102, 124, 198, 155, 107, 1, 7, 186, 236, 55, 159, 154, 41, 1, 4, 171, 74, 1, 13, 186, 107, 1, 14, 186, 140, 1, 6, 154, 130, 5, 0, 145, 103, 124, 2, 155, 102, 124, 194, 155, 8, 1, 7, 171, 41, 1, 6, 186, 74, 1, 31, 186, 107, 1, 31, 186, 99, 48, 159, 154, 8, 1, 3, 235, 41, 1, 31, 250, 74, 1, 31, 250, 107, 1, 31, 218, 8, 36, 0, 169, 10, 44, 1, 169, 192, 3, 95, 214]
private theorem file_slice :
    (SecpArtifact.elf.toList.drop 3496).take 316 = fileBytes := by rfl

private theorem slice_byte (bytes : Array Nat) (start size i : Nat) (data : List Nat)
    (bound : i < size) (binding : (bytes.toList.drop start).take size = data) :
    byte bytes (start + i) = data.getD i 0 := by
  rw [← binding]
  simp only [byte, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt bound, List.getElem?_drop, Array.getElem?_toList]

private theorem ranges :
    words.all (fun c => decide (7592 ≤ c.1 ∧ c.1 + 4 ≤ 7908)) = true := by decide

private def wordOK (c : Nat × Nat) : Bool :=
  (List.range 4).all fun i =>
    fileBytes.getD (c.1 - 7592 + i) 0 == (c.2 >>> (8 * i)) % 256

private theorem join (xs : List (Nat × Nat)) (start size : Nat)
    (head : ((xs.drop start).take size).all wordOK = true)
    (tail : (xs.drop (start + size)).all wordOK = true) :
    (xs.drop start).all wordOK = true := by
  have tail' : ((xs.drop start).drop size).all wordOK = true := by
    simpa only [List.drop_drop, Nat.add_comm] using tail
  rw [← List.take_append_drop size (xs.drop start), List.all_append, head, tail'] <;> rfl

set_option maxHeartbeats 1000000 in
private theorem chunk_0 : ((words.drop 0).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_8 : ((words.drop 8).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_16 : ((words.drop 16).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_24 : ((words.drop 24).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_32 : ((words.drop 32).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_40 : ((words.drop 40).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_48 : ((words.drop 48).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_56 : ((words.drop 56).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_64 : ((words.drop 64).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_72 : ((words.drop 72).take 7).all wordOK = true := by rfl
private theorem end_check : (words.drop 79).all wordOK = true := by rfl

private theorem words_checked : words.all wordOK = true := by
  change (words.drop 0).all wordOK = true
  refine join _ 0 8 chunk_0 ?_
  refine join _ 8 8 chunk_8 ?_
  refine join _ 16 8 chunk_16 ?_
  refine join _ 24 8 chunk_24 ?_
  refine join _ 32 8 chunk_32 ?_
  refine join _ 40 8 chunk_40 ?_
  refine join _ 48 8 chunk_48 ?_
  refine join _ 56 8 chunk_56 ?_
  refine join _ 64 8 chunk_64 ?_
  refine join _ 72 7 chunk_72 ?_
  exact end_check

theorem code_binds : Lean_D234_SecpSqrAlt_c27E17.CodeBinds SecpArtifact.elf := by
  intro c hc i hi
  rw [words_match] at hc
  have range := of_decide_eq_true (List.all_eq_true.mp ranges c hc)
  have bound : c.1 - 7592 + i < 316 := by omega
  have byteEq := slice_byte SecpArtifact.elf 3496 316
    (c.1 - 7592 + i) fileBytes bound file_slice
  have position : 3496 + (c.1 - 7592 + i) = 1592 + (c.1 - 5688) + i := by omega
  rw [position] at byteEq
  exact byteEq.trans (beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked c hc) i (List.mem_range.mpr hi)))

theorem code_image (base : BitVec 64) {c : Nat × Nat}
    (member : c ∈ Lean_D234_SecpSqrAlt_c27E17.codeVAs) (i : Nat) (hi : i < 4) :
    referenceImageI SecpArtifact.elf base (fun _ => 0) (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) :=
  Lean_D234_SecpSqrAlt_c27E17.code_image _ image_binds code_binds base _ member i hi

#print axioms image_binds
#print axioms scoped_image
#print axioms code_binds
#print axioms code_image
end PipeLean_D234_SecpSqrAlt_c27.ImageBinding
