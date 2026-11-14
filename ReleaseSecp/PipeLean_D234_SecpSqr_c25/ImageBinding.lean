import Lean_D234_SecpSqr_c25E17.Fetch
import SecpArtifact.Elf
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSqr_c25.ImageBinding
open ArmCert.Translate.Model.StaticPie

theorem image_binds : Binds SecpArtifact.elf Lean_D234_SecpSqr_c25Scoped.slices := SecpArtifact.sub_binds
theorem scoped_image : ScopedAdmitted SecpArtifact.elf Lean_D234_SecpSqr_c25Scoped.closure Lean_D234_SecpSqr_c25Scoped.slices.rela :=
  Lean_D234_SecpSqr_c25Scoped.lean_d234_secpsqr_c25_scoped _ image_binds

private def words : List (Nat × Nat) := [(7048, 2839555114), (7052, 2839622700), (7056, 2611641666), (7060, 3546348878), (7064, 2611903939), (7068, 2611903822), (7072, 2869855298), (7076, 3546283470), (7080, 2584608867), (7084, 2611707236), (7088, 3546348910), (7092, 2611903941), (7096, 2611903854), (7100, 2601221455), (7104, 2613804368), (7108, 2869855364), (7112, 3546283470), (7116, 2584608933), (7120, 2869887471), (7124, 3121611280), (7128, 2585723045), (7132, 2869887075), (7136, 3121610884), (7140, 2585723045), (7144, 2611772806), (7148, 3546348942), (7152, 2611903943), (7156, 2611903886), (7160, 2869855430), (7164, 3546283470), (7168, 2584608999), (7172, 2611838376), (7176, 3546348974), (7180, 2611903945), (7184, 2611903918), (7188, 2601352591), (7192, 2613935504), (7196, 2869855496), (7200, 3546283470), (7204, 2584609065), (7208, 2869887471), (7212, 3121611280), (7216, 2585723177), (7220, 2869887207), (7224, 3121611016), (7228, 2585723177), (7232, 3943432522), (7236, 4195156331), (7240, 3667862512), (7244, 3390046538), (7248, 3943694666), (7252, 3390046571), (7256, 3658482027), (7260, 2869166278), (7264, 3120890087), (7268, 3122594056), (7272, 2585723177), (7276, 2611641676), (7280, 3546348869), (7284, 2611313837), (7288, 2611313989), (7292, 2869265804), (7296, 3546283173), (7300, 2584019373), (7304, 2611707247), (7308, 3546348901), (7312, 2611313838), (7316, 2611314021), (7320, 2601221444), (7324, 2613804368), (7328, 2869265903), (7332, 3546283173), (7336, 2584019406), (7340, 2869166212), (7344, 3121611280), (7348, 2585723342), (7352, 2869166509), (7356, 3121611247), (7360, 2585723342), (7364, 2869297220), (7368, 3121021029), (7372, 3121086662), (7376, 3121152231), (7380, 3667862512), (7384, 3943432324), (7388, 4195156133), (7392, 4195287238), (7396, 4195221735), (7400, 3121611016), (7404, 2584740137), (7408, 3531635249), (7412, 2992636464), (7416, 2600893962), (7420, 2613476877), (7424, 2453699814), (7428, 3546348775), (7432, 2600893995), (7436, 2600933926), (7440, 2869330283), (7444, 3546348742), (7448, 2584084718), (7452, 2601025036), (7456, 2613607944), (7460, 2453699878), (7464, 3546348839), (7468, 2600893993), (7472, 2600933926), (7476, 2869330217), (7480, 3546348742), (7484, 2584084719), (7488, 2869559362), (7492, 3121283171), (7496, 3121348740), (7500, 3121152165), (7504, 2594125798), (7508, 2869756003), (7512, 3121479812), (7516, 3121086629), (7520, 2584674502), (7524, 2432697542), (7528, 2600893994), (7532, 3546348747), (7536, 2869330250), (7540, 2584413163), (7544, 2869559362), (7548, 3121283171), (7552, 3122593924), (7556, 3122593957), (7560, 2594124304), (7564, 3943694402), (7568, 4196335715), (7572, 4196335748), (7576, 3659464869), (7580, 2835352578), (7584, 2835420164), (7588, 3596551104)]
private theorem words_match : Lean_D234_SecpSqr_c25E17.codeVAs = words := by rfl

private def fileBytes : List Nat := [42, 44, 64, 169, 44, 52, 65, 169, 66, 125, 170, 155, 78, 253, 96, 211, 195, 125, 174, 155, 78, 125, 174, 155, 66, 132, 14, 171, 206, 253, 95, 211, 99, 0, 14, 154, 100, 125, 171, 155, 110, 253, 96, 211, 197, 125, 174, 155, 110, 125, 174, 155, 79, 125, 11, 155, 80, 125, 203, 155, 132, 132, 14, 171, 206, 253, 95, 211, 165, 0, 14, 154, 239, 1, 15, 171, 16, 2, 16, 186, 165, 0, 31, 154, 99, 0, 15, 171, 132, 0, 16, 186, 165, 0, 31, 154, 134, 125, 172, 155, 142, 253, 96, 211, 199, 125, 174, 155, 142, 125, 174, 155, 198, 132, 14, 171, 206, 253, 95, 211, 231, 0, 14, 154, 168, 125, 173, 155, 174, 253, 96, 211, 201, 125, 174, 155, 174, 125, 174, 155, 143, 125, 13, 155, 144, 125, 205, 155, 8, 133, 14, 171, 206, 253, 95, 211, 41, 1, 14, 154, 239, 1, 15, 171, 16, 2, 16, 186, 41, 1, 31, 154, 231, 0, 15, 171, 8, 1, 16, 186, 41, 1, 31, 154, 74, 1, 12, 235, 107, 1, 13, 250, 240, 35, 159, 218, 74, 1, 16, 202, 74, 1, 16, 235, 107, 1, 16, 202, 107, 1, 16, 218, 198, 0, 4, 171, 231, 0, 5, 186, 8, 1, 31, 186, 41, 1, 31, 154, 76, 125, 170, 155, 69, 253, 96, 211, 173, 124, 165, 155, 69, 125, 165, 155, 140, 133, 5, 171, 165, 252, 95, 211, 173, 1, 5, 154, 111, 125, 171, 155, 101, 253, 96, 211, 174, 124, 165, 155, 101, 125, 165, 155, 68, 125, 11, 155, 80, 125, 203, 155, 239, 133, 5, 171, 165, 252, 95, 211, 206, 1, 5, 154, 132, 0, 4, 171, 16, 2, 16, 186, 206, 1, 31, 154, 173, 1, 4, 171, 239, 1, 16, 186, 206, 1, 31, 154, 68, 0, 6, 171, 101, 0, 7, 186, 198, 0, 8, 186, 231, 0, 9, 186, 240, 35, 159, 218, 132, 0, 12, 235, 165, 0, 13, 250, 198, 0, 15, 250, 231, 0, 14, 250, 8, 1, 16, 186, 41, 1, 16, 154, 49, 122, 128, 210, 48, 2, 96, 178, 10, 126, 6, 155, 13, 126, 198, 155, 230, 124, 64, 146, 231, 252, 96, 211, 43, 126, 6, 155, 38, 26, 7, 155, 107, 129, 6, 171, 198, 252, 96, 211, 238, 0, 6, 154, 12, 126, 8, 155, 8, 126, 200, 155, 38, 125, 64, 146, 39, 253, 96, 211, 41, 126, 6, 155, 38, 26, 7, 155, 41, 129, 6, 171, 198, 252, 96, 211, 239, 0, 6, 154, 66, 0, 10, 171, 99, 0, 11, 186, 132, 0, 12, 186, 165, 0, 9, 186, 230, 55, 159, 154, 99, 0, 13, 171, 132, 0, 14, 186, 165, 0, 8, 186, 198, 0, 15, 154, 198, 4, 0, 145, 42, 126, 6, 155, 203, 252, 96, 211, 74, 129, 6, 171, 235, 3, 11, 154, 66, 0, 10, 171, 99, 0, 11, 186, 132, 0, 31, 186, 165, 0, 31, 186, 16, 50, 159, 154, 66, 0, 16, 235, 99, 0, 31, 250, 132, 0, 31, 250, 165, 0, 31, 218, 2, 12, 0, 169, 4, 20, 1, 169, 192, 3, 95, 214]
private theorem file_slice :
    (SecpArtifact.elf.toList.drop 2952).take 544 = fileBytes := by rfl

private theorem slice_byte (bytes : Array Nat) (start size i : Nat) (data : List Nat)
    (bound : i < size) (binding : (bytes.toList.drop start).take size = data) :
    byte bytes (start + i) = data.getD i 0 := by
  rw [← binding]
  simp only [byte, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt bound, List.getElem?_drop, Array.getElem?_toList]

private theorem ranges :
    words.all (fun c => decide (7048 ≤ c.1 ∧ c.1 + 4 ≤ 7592)) = true := by decide

private def wordOK (c : Nat × Nat) : Bool :=
  (List.range 4).all fun i =>
    fileBytes.getD (c.1 - 7048 + i) 0 == (c.2 >>> (8 * i)) % 256

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
private theorem chunk_72 : ((words.drop 72).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_80 : ((words.drop 80).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_88 : ((words.drop 88).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_96 : ((words.drop 96).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_104 : ((words.drop 104).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_112 : ((words.drop 112).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_120 : ((words.drop 120).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_128 : ((words.drop 128).take 8).all wordOK = true := by rfl
private theorem end_check : (words.drop 136).all wordOK = true := by rfl

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
  refine join _ 72 8 chunk_72 ?_
  refine join _ 80 8 chunk_80 ?_
  refine join _ 88 8 chunk_88 ?_
  refine join _ 96 8 chunk_96 ?_
  refine join _ 104 8 chunk_104 ?_
  refine join _ 112 8 chunk_112 ?_
  refine join _ 120 8 chunk_120 ?_
  refine join _ 128 8 chunk_128 ?_
  exact end_check

theorem code_binds : Lean_D234_SecpSqr_c25E17.CodeBinds SecpArtifact.elf := by
  intro c hc i hi
  rw [words_match] at hc
  have range := of_decide_eq_true (List.all_eq_true.mp ranges c hc)
  have bound : c.1 - 7048 + i < 544 := by omega
  have byteEq := slice_byte SecpArtifact.elf 2952 544
    (c.1 - 7048 + i) fileBytes bound file_slice
  have position : 2952 + (c.1 - 7048 + i) = 1592 + (c.1 - 5688) + i := by omega
  rw [position] at byteEq
  exact byteEq.trans (beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked c hc) i (List.mem_range.mpr hi)))

theorem code_image (base : BitVec 64) {c : Nat × Nat}
    (member : c ∈ Lean_D234_SecpSqr_c25E17.codeVAs) (i : Nat) (hi : i < 4) :
    referenceImageI SecpArtifact.elf base (fun _ => 0) (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) :=
  Lean_D234_SecpSqr_c25E17.code_image _ image_binds code_binds base _ member i hi

#print axioms image_binds
#print axioms scoped_image
#print axioms code_binds
#print axioms code_image
end PipeLean_D234_SecpSqr_c25.ImageBinding
