import Lean_D234_SecpMulAlt_c20E17.Fetch
import SecpArtifact.Elf
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpMulAlt_c20.ImageBinding
open ArmCert.Translate.Model.StaticPie

theorem image_binds : Binds SecpArtifact.elf Lean_D234_SecpMulAlt_c20Scoped.slices := SecpArtifact.sub_binds
theorem scoped_image : ScopedAdmitted SecpArtifact.elf Lean_D234_SecpMulAlt_c20Scoped.closure Lean_D234_SecpMulAlt_c20Scoped.slices.rela :=
  Lean_D234_SecpMulAlt_c20Scoped.lean_d234_secpmulalt_c20_scoped _ image_binds

private def words : List (Nat × Nat) := [(6644, 2839547939), (6648, 2839552071), (6652, 2600959084), (6656, 2613541997), (6660, 2601024619), (6664, 2613607534), (6668, 2869625261), (6672, 2839619657), (6676, 2601090155), (6680, 2613673071), (6684, 3121283534), (6688, 2601155691), (6692, 2613738608), (6696, 3121283567), (6700, 2585723408), (6704, 2839615525), (6708, 2600959115), (6712, 2869625261), (6716, 2601024651), (6720, 3121283534), (6724, 2601090187), (6728, 3121283567), (6732, 2601155723), (6736, 3121283600), (6740, 2613738627), (6744, 2585722979), (6748, 2613542027), (6752, 2869625294), (6756, 2613607563), (6760, 3121283567), (6764, 2613673099), (6768, 3121283600), (6772, 2585722979), (6776, 2600959147), (6780, 2869625294), (6784, 2601024683), (6788, 3121283567), (6792, 2601090219), (6796, 3121283600), (6800, 2601155755), (6804, 3121283171), (6808, 2613738660), (6812, 2585723012), (6816, 2613542059), (6820, 2869625327), (6824, 2613607595), (6828, 3121283600), (6832, 2613673131), (6836, 3121283171), (6840, 2585723012), (6844, 2600959179), (6848, 2869625327), (6852, 2601024715), (6856, 3121283600), (6860, 2601090251), (6864, 3121283171), (6868, 2601155787), (6872, 3121283204), (6876, 2613738693), (6880, 2585723045), (6884, 2613542091), (6888, 2869625360), (6892, 2613607627), (6896, 3121283171), (6900, 2613673163), (6904, 3121283204), (6908, 2585723045), (6912, 3531635239), (6916, 2992636135), (6920, 2601549035), (6924, 2614131945), (6928, 2869625228), (6932, 2600697067), (6936, 2613279971), (6940, 3121283501), (6944, 2600762603), (6948, 2613345508), (6952, 3121283534), (6956, 2600828139), (6960, 2613411045), (6964, 3121283567), (6968, 2594125808), (6972, 2869494189), (6976, 3120759246), (6980, 3120824815), (6984, 2584019472), (6988, 2432697864), (6992, 2601024747), (6996, 2613607657), (7000, 2869625228), (7004, 3121152429), (7008, 3122594254), (7012, 3122594287), (7016, 2594124007), (7020, 3943104908), (7024, 4196336045), (7028, 4196336078), (7032, 3659465199), (7036, 2835362828), (7040, 2835430414), (7044, 3596551104)]
private theorem words_match : Lean_D234_SecpMulAlt_c20E17.codeVAs = words := by rfl

private def fileBytes : List Nat := [35, 16, 64, 169, 71, 32, 64, 169, 108, 124, 7, 155, 109, 124, 199, 155, 107, 124, 8, 155, 110, 124, 200, 155, 173, 1, 11, 171, 73, 40, 65, 169, 107, 124, 9, 155, 111, 124, 201, 155, 206, 1, 11, 186, 107, 124, 10, 155, 112, 124, 202, 155, 239, 1, 11, 186, 16, 2, 31, 154, 37, 24, 65, 169, 139, 124, 7, 155, 173, 1, 11, 171, 139, 124, 8, 155, 206, 1, 11, 186, 139, 124, 9, 155, 239, 1, 11, 186, 139, 124, 10, 155, 16, 2, 11, 186, 131, 124, 202, 155, 99, 0, 31, 154, 139, 124, 199, 155, 206, 1, 11, 171, 139, 124, 200, 155, 239, 1, 11, 186, 139, 124, 201, 155, 16, 2, 11, 186, 99, 0, 31, 154, 171, 124, 7, 155, 206, 1, 11, 171, 171, 124, 8, 155, 239, 1, 11, 186, 171, 124, 9, 155, 16, 2, 11, 186, 171, 124, 10, 155, 99, 0, 11, 186, 164, 124, 202, 155, 132, 0, 31, 154, 171, 124, 199, 155, 239, 1, 11, 171, 171, 124, 200, 155, 16, 2, 11, 186, 171, 124, 201, 155, 99, 0, 11, 186, 132, 0, 31, 154, 203, 124, 7, 155, 239, 1, 11, 171, 203, 124, 8, 155, 16, 2, 11, 186, 203, 124, 9, 155, 99, 0, 11, 186, 203, 124, 10, 155, 132, 0, 11, 186, 197, 124, 202, 155, 165, 0, 31, 154, 203, 124, 199, 155, 16, 2, 11, 171, 203, 124, 200, 155, 99, 0, 11, 186, 203, 124, 201, 155, 132, 0, 11, 186, 165, 0, 31, 154, 39, 122, 128, 210, 231, 0, 96, 178, 235, 124, 16, 155, 233, 124, 208, 155, 140, 1, 11, 171, 235, 124, 3, 155, 227, 124, 195, 155, 173, 1, 11, 186, 235, 124, 4, 155, 228, 124, 196, 155, 206, 1, 11, 186, 235, 124, 5, 155, 229, 124, 197, 155, 239, 1, 11, 186, 240, 55, 159, 154, 173, 1, 9, 171, 206, 1, 3, 186, 239, 1, 4, 186, 16, 2, 5, 154, 8, 6, 0, 145, 235, 124, 8, 155, 233, 124, 200, 155, 140, 1, 11, 171, 173, 1, 9, 186, 206, 1, 31, 186, 239, 1, 31, 186, 231, 48, 159, 154, 140, 1, 7, 235, 173, 1, 31, 250, 206, 1, 31, 250, 239, 1, 31, 218, 12, 52, 0, 169, 14, 60, 1, 169, 192, 3, 95, 214]
private theorem file_slice :
    (SecpArtifact.elf.toList.drop 2548).take 404 = fileBytes := by rfl

private theorem slice_byte (bytes : Array Nat) (start size i : Nat) (data : List Nat)
    (bound : i < size) (binding : (bytes.toList.drop start).take size = data) :
    byte bytes (start + i) = data.getD i 0 := by
  rw [← binding]
  simp only [byte, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt bound, List.getElem?_drop, Array.getElem?_toList]

private theorem ranges :
    words.all (fun c => decide (6644 ≤ c.1 ∧ c.1 + 4 ≤ 7048)) = true := by decide

private def wordOK (c : Nat × Nat) : Bool :=
  (List.range 4).all fun i =>
    fileBytes.getD (c.1 - 6644 + i) 0 == (c.2 >>> (8 * i)) % 256

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
private theorem chunk_96 : ((words.drop 96).take 5).all wordOK = true := by rfl
private theorem end_check : (words.drop 101).all wordOK = true := by rfl

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
  refine join _ 96 5 chunk_96 ?_
  exact end_check

theorem code_binds : Lean_D234_SecpMulAlt_c20E17.CodeBinds SecpArtifact.elf := by
  intro c hc i hi
  rw [words_match] at hc
  have range := of_decide_eq_true (List.all_eq_true.mp ranges c hc)
  have bound : c.1 - 6644 + i < 404 := by omega
  have byteEq := slice_byte SecpArtifact.elf 2548 404
    (c.1 - 6644 + i) fileBytes bound file_slice
  have position : 2548 + (c.1 - 6644 + i) = 1592 + (c.1 - 5688) + i := by omega
  rw [position] at byteEq
  exact byteEq.trans (beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked c hc) i (List.mem_range.mpr hi)))

theorem code_image (base : BitVec 64) {c : Nat × Nat}
    (member : c ∈ Lean_D234_SecpMulAlt_c20E17.codeVAs) (i : Nat) (hi : i < 4) :
    referenceImageI SecpArtifact.elf base (fun _ => 0) (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) :=
  Lean_D234_SecpMulAlt_c20E17.code_image _ image_binds code_binds base _ member i hi

#print axioms image_binds
#print axioms scoped_image
#print axioms code_binds
#print axioms code_image
end PipeLean_D234_SecpMulAlt_c20.ImageBinding
