import Lean_D234_SecpMul_c16E17.Fetch
import SecpArtifact.Elf
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpMul_c16.ImageBinding
open ArmCert.Translate.Model.StaticPie

theorem image_binds : Binds SecpArtifact.elf Lean_D234_SecpMul_c16Scoped.slices := SecpArtifact.sub_binds
theorem scoped_image : ScopedAdmitted SecpArtifact.elf Lean_D234_SecpMul_c16Scoped.closure Lean_D234_SecpMul_c16Scoped.slices.rela :=
  Lean_D234_SecpMul_c16Scoped.lean_d234_secpmul_c16_scoped _ image_binds

private def words : List (Nat × Nat) := [(6012, 2839547939), (6016, 2839550021), (6020, 2600828007), (6024, 2613410920), (6028, 2600893577), (6032, 2613476490), (6036, 3942842500), (6040, 3666093188), (6044, 3667862512), (6048, 2869428521), (6052, 2585723210), (6056, 3943039139), (6060, 3666027619), (6064, 3666878992), (6068, 2600696975), (6072, 2613279875), (6076, 2869493992), (6080, 3121217833), (6084, 2585723210), (6088, 2969568799), (6092, 3390046703), (6096, 3121086952), (6100, 3390046307), (6104, 3121152105), (6108, 2584740170), (6112, 2839613475), (6116, 2839615557), (6120, 2600828011), (6124, 2613410924), (6128, 2600893581), (6132, 2613476494), (6136, 3942842500), (6140, 3666093188), (6144, 3667862512), (6148, 2869690797), (6152, 2585723342), (6156, 3943039139), (6160, 3666027619), (6164, 3666878992), (6168, 2600696975), (6172, 2613279875), (6176, 2869756268), (6180, 3121480109), (6184, 2585723342), (6188, 2969568799), (6192, 3390046703), (6196, 3121349100), (6200, 3390046307), (6204, 3121414253), (6208, 2584740302), (6212, 2839613475), (6216, 2839560239), (6220, 3943628899), (6224, 4195352708), (6228, 3667862512), (6232, 2839561295), (6236, 3942973925), (6240, 4194697766), (6244, 3667862513), (6248, 3390046307), (6252, 3943694435), (6256, 3390046340), (6260, 3658481796), (6264, 3390111909), (6268, 3943760037), (6272, 3390111942), (6276, 3658547398), (6280, 3390046768), (6284, 2869494123), (6288, 3121217932), (6292, 3122594221), (6296, 2585723342), (6300, 2600828002), (6304, 2613410929), (6308, 2600893583), (6312, 2613476481), (6316, 3942842500), (6320, 3666093188), (6324, 3667862505), (6328, 2870018543), (6332, 2585722913), (6336, 3943039142), (6340, 3666224326), (6344, 3666420009), (6348, 2600893573), (6352, 2613476486), (6356, 2869887057), (6360, 3120628207), (6364, 2585722913), (6368, 2969568575), (6372, 3389587621), (6376, 3121676465), (6380, 3389587654), (6384, 3121545423), (6388, 2584281121), (6392, 2869363049), (6396, 3121086858), (6400, 3121283499), (6404, 3121349068), (6408, 3122594221), (6412, 2585723342), (6416, 2969568799), (6420, 3390046274), (6424, 3121152073), (6428, 3390046769), (6432, 3121218090), (6436, 3390046703), (6440, 3121283563), (6444, 3390046241), (6448, 3121348652), (6452, 3121611181), (6456, 2584740302), (6460, 3531635248), (6464, 2992636417), (6468, 2601221155), (6472, 2613804069), (6476, 2453699983), (6480, 3546348930), (6484, 2601483780), (6488, 2600615439), (6492, 2869919876), (6496, 3546349039), (6500, 2584674374), (6504, 2601352235), (6508, 2613935149), (6512, 2453700047), (6516, 3546348994), (6520, 2601483788), (6524, 2600615439), (6528, 2869920140), (6532, 3546349039), (6536, 2584674382), (6540, 2869100775), (6544, 3120824584), (6548, 3121283369), (6552, 3121348938), (6556, 2594125803), (6560, 2869231880), (6564, 3120955689), (6568, 3121414474), (6572, 2584609131), (6576, 2432697713), (6580, 2601614851), (6584, 3546349092), (6588, 2870050915), (6592, 2583954404), (6596, 2869100775), (6600, 3120824584), (6604, 3122594089), (6608, 3122594122), (6612, 2594123809), (6616, 3942711527), (6620, 4196335880), (6624, 4196335913), (6628, 3659465034), (6632, 2835357703), (6636, 2835425289), (6640, 3596551104)]
private theorem words_match : Lean_D234_SecpMul_c16E17.codeVAs = words := by rfl

private def fileBytes : List Nat := [35, 16, 64, 169, 69, 24, 64, 169, 103, 124, 5, 155, 104, 124, 197, 155, 137, 124, 6, 155, 138, 124, 198, 155, 132, 0, 3, 235, 132, 36, 132, 218, 240, 35, 159, 218, 41, 1, 8, 171, 74, 1, 31, 154, 163, 0, 6, 235, 99, 36, 131, 218, 16, 34, 144, 218, 143, 124, 3, 155, 131, 124, 195, 155, 232, 0, 9, 171, 41, 1, 10, 186, 74, 1, 31, 154, 31, 6, 0, 177, 239, 1, 16, 202, 232, 1, 8, 186, 99, 0, 16, 202, 105, 0, 9, 186, 74, 1, 16, 154, 35, 16, 65, 169, 69, 24, 65, 169, 107, 124, 5, 155, 108, 124, 197, 155, 141, 124, 6, 155, 142, 124, 198, 155, 132, 0, 3, 235, 132, 36, 132, 218, 240, 35, 159, 218, 173, 1, 12, 171, 206, 1, 31, 154, 163, 0, 6, 235, 99, 36, 131, 218, 16, 34, 144, 218, 143, 124, 3, 155, 131, 124, 195, 155, 108, 1, 13, 171, 173, 1, 14, 186, 206, 1, 31, 154, 31, 6, 0, 177, 239, 1, 16, 202, 236, 1, 12, 186, 99, 0, 16, 202, 109, 0, 13, 186, 206, 1, 16, 154, 35, 16, 65, 169, 47, 64, 64, 169, 99, 0, 15, 235, 132, 0, 16, 250, 240, 35, 159, 218, 79, 68, 64, 169, 229, 1, 5, 235, 38, 2, 6, 250, 241, 35, 159, 218, 99, 0, 16, 202, 99, 0, 16, 235, 132, 0, 16, 202, 132, 0, 16, 218, 165, 0, 17, 202, 165, 0, 17, 235, 198, 0, 17, 202, 198, 0, 17, 218, 48, 2, 16, 202, 107, 1, 9, 171, 140, 1, 10, 186, 173, 1, 31, 186, 206, 1, 31, 154, 98, 124, 5, 155, 113, 124, 197, 155, 143, 124, 6, 155, 129, 124, 198, 155, 132, 0, 3, 235, 132, 36, 132, 218, 233, 35, 159, 218, 239, 1, 17, 171, 33, 0, 31, 154, 166, 0, 6, 235, 198, 36, 134, 218, 41, 33, 137, 218, 133, 124, 6, 155, 134, 124, 198, 155, 81, 0, 15, 171, 239, 1, 1, 186, 33, 0, 31, 154, 63, 5, 0, 177, 165, 0, 9, 202, 177, 0, 17, 186, 198, 0, 9, 202, 207, 0, 15, 186, 33, 0, 9, 154, 105, 1, 7, 171, 138, 1, 8, 186, 171, 1, 11, 186, 204, 1, 12, 186, 173, 1, 31, 186, 206, 1, 31, 154, 31, 6, 0, 177, 66, 0, 16, 202, 73, 0, 9, 186, 49, 2, 16, 202, 42, 2, 10, 186, 239, 1, 16, 202, 235, 1, 11, 186, 33, 0, 16, 202, 44, 0, 12, 186, 173, 1, 16, 186, 206, 1, 16, 154, 48, 122, 128, 210, 1, 2, 96, 178, 35, 124, 11, 155, 37, 124, 203, 155, 143, 125, 64, 146, 130, 253, 96, 211, 4, 126, 15, 155, 15, 62, 2, 155, 132, 128, 15, 171, 239, 253, 96, 211, 70, 0, 15, 154, 43, 124, 13, 155, 45, 124, 205, 155, 207, 125, 64, 146, 194, 253, 96, 211, 12, 126, 15, 155, 15, 62, 2, 155, 140, 129, 15, 171, 239, 253, 96, 211, 78, 0, 15, 154, 231, 0, 3, 171, 8, 1, 4, 186, 41, 1, 11, 186, 74, 1, 12, 186, 235, 55, 159, 154, 8, 1, 5, 171, 41, 1, 6, 186, 74, 1, 13, 186, 107, 1, 14, 154, 113, 5, 0, 145, 3, 126, 17, 155, 36, 254, 96, 211, 99, 128, 17, 171, 228, 3, 4, 154, 231, 0, 3, 171, 8, 1, 4, 186, 41, 1, 31, 186, 74, 1, 31, 186, 33, 48, 159, 154, 231, 0, 1, 235, 8, 1, 31, 250, 41, 1, 31, 250, 74, 1, 31, 218, 7, 32, 0, 169, 9, 40, 1, 169, 192, 3, 95, 214]
private theorem file_slice :
    (SecpArtifact.elf.toList.drop 1916).take 632 = fileBytes := by rfl

private theorem slice_byte (bytes : Array Nat) (start size i : Nat) (data : List Nat)
    (bound : i < size) (binding : (bytes.toList.drop start).take size = data) :
    byte bytes (start + i) = data.getD i 0 := by
  rw [← binding]
  simp only [byte, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt bound, List.getElem?_drop, Array.getElem?_toList]

private theorem ranges :
    words.all (fun c => decide (6012 ≤ c.1 ∧ c.1 + 4 ≤ 6644)) = true := by decide

private def wordOK (c : Nat × Nat) : Bool :=
  (List.range 4).all fun i =>
    fileBytes.getD (c.1 - 6012 + i) 0 == (c.2 >>> (8 * i)) % 256

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
set_option maxHeartbeats 1000000 in
private theorem chunk_136 : ((words.drop 136).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_144 : ((words.drop 144).take 8).all wordOK = true := by rfl
set_option maxHeartbeats 1000000 in
private theorem chunk_152 : ((words.drop 152).take 6).all wordOK = true := by rfl
private theorem end_check : (words.drop 158).all wordOK = true := by rfl

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
  refine join _ 136 8 chunk_136 ?_
  refine join _ 144 8 chunk_144 ?_
  refine join _ 152 6 chunk_152 ?_
  exact end_check

theorem code_binds : Lean_D234_SecpMul_c16E17.CodeBinds SecpArtifact.elf := by
  intro c hc i hi
  rw [words_match] at hc
  have range := of_decide_eq_true (List.all_eq_true.mp ranges c hc)
  have bound : c.1 - 6012 + i < 632 := by omega
  have byteEq := slice_byte SecpArtifact.elf 1916 632
    (c.1 - 6012 + i) fileBytes bound file_slice
  have position : 1916 + (c.1 - 6012 + i) = 1592 + (c.1 - 5688) + i := by omega
  rw [position] at byteEq
  exact byteEq.trans (beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked c hc) i (List.mem_range.mpr hi)))

theorem code_image (base : BitVec 64) {c : Nat × Nat}
    (member : c ∈ Lean_D234_SecpMul_c16E17.codeVAs) (i : Nat) (hi : i < 4) :
    referenceImageI SecpArtifact.elf base (fun _ => 0) (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) :=
  Lean_D234_SecpMul_c16E17.code_image _ image_binds code_binds base _ member i hi

#print axioms image_binds
#print axioms scoped_image
#print axioms code_binds
#print axioms code_image
end PipeLean_D234_SecpMul_c16.ImageBinding
