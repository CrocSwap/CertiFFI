import Lean_D234_SecpCmul_c29E17.Fetch
import SecpArtifact.Elf
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpCmul_c29.ImageBinding
open ArmCert.Translate.Model.StaticPie

theorem image_binds : Binds SecpArtifact.elf Lean_D234_SecpCmul_c29Scoped.slices := SecpArtifact.sub_binds
theorem scoped_image : ScopedAdmitted SecpArtifact.elf Lean_D234_SecpCmul_c29Scoped.closure Lean_D234_SecpCmul_c29Scoped.slices.rela :=
  Lean_D234_SecpCmul_c29Scoped.lean_d234_secpcmul_c29_scoped _ image_binds

private def words : List (Nat × Nat) := [(7908, 2839552071), (7912, 2839619657), (7916, 2600959011), (7920, 2601024548), (7924, 2601090085), (7928, 2601155622), (7932, 2613541927), (7936, 2613607464), (7940, 2613673001), (7944, 2613738538), (7948, 2869362820), (7952, 3121086629), (7956, 3121152198), (7960, 3122594122), (7964, 2432697674), (7968, 3531635241), (7972, 2992636201), (7976, 2601090375), (7980, 2613673288), (7984, 2869362787), (7988, 3121086596), (7992, 3122593957), (7996, 3122593990), (8000, 2594124073), (8004, 3943235683), (8008, 4196335748), (8012, 4196335781), (8016, 3659464902), (8020, 2835353603), (8024, 2835421189), (8028, 3596551104)]
private theorem words_match : Lean_D234_SecpCmul_c29E17.codeVAs = words := by rfl

private def fileBytes : List Nat := [71, 32, 64, 169, 73, 40, 65, 169, 35, 124, 7, 155, 36, 124, 8, 155, 37, 124, 9, 155, 38, 124, 10, 155, 39, 124, 199, 155, 40, 124, 200, 155, 41, 124, 201, 155, 42, 124, 202, 155, 132, 0, 7, 171, 165, 0, 8, 186, 198, 0, 9, 186, 74, 1, 31, 186, 74, 5, 0, 145, 41, 122, 128, 210, 41, 1, 96, 178, 71, 125, 9, 155, 72, 125, 201, 155, 99, 0, 7, 171, 132, 0, 8, 186, 165, 0, 31, 186, 198, 0, 31, 186, 41, 49, 159, 154, 99, 0, 9, 235, 132, 0, 31, 250, 165, 0, 31, 250, 198, 0, 31, 218, 3, 16, 0, 169, 5, 24, 1, 169, 192, 3, 95, 214]
private theorem file_slice :
    (SecpArtifact.elf.toList.drop 3812).take 124 = fileBytes := by rfl

private theorem slice_byte (bytes : Array Nat) (start size i : Nat) (data : List Nat)
    (bound : i < size) (binding : (bytes.toList.drop start).take size = data) :
    byte bytes (start + i) = data.getD i 0 := by
  rw [← binding]
  simp only [byte, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt bound, List.getElem?_drop, Array.getElem?_toList]

private theorem ranges :
    words.all (fun c => decide (7908 ≤ c.1 ∧ c.1 + 4 ≤ 8032)) = true := by decide

private def wordOK (c : Nat × Nat) : Bool :=
  (List.range 4).all fun i =>
    fileBytes.getD (c.1 - 7908 + i) 0 == (c.2 >>> (8 * i)) % 256

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
private theorem chunk_24 : ((words.drop 24).take 7).all wordOK = true := by rfl
private theorem end_check : (words.drop 31).all wordOK = true := by rfl

private theorem words_checked : words.all wordOK = true := by
  change (words.drop 0).all wordOK = true
  refine join _ 0 8 chunk_0 ?_
  refine join _ 8 8 chunk_8 ?_
  refine join _ 16 8 chunk_16 ?_
  refine join _ 24 7 chunk_24 ?_
  exact end_check

theorem code_binds : Lean_D234_SecpCmul_c29E17.CodeBinds SecpArtifact.elf := by
  intro c hc i hi
  rw [words_match] at hc
  have range := of_decide_eq_true (List.all_eq_true.mp ranges c hc)
  have bound : c.1 - 7908 + i < 124 := by omega
  have byteEq := slice_byte SecpArtifact.elf 3812 124
    (c.1 - 7908 + i) fileBytes bound file_slice
  have position : 3812 + (c.1 - 7908 + i) = 1592 + (c.1 - 5688) + i := by omega
  rw [position] at byteEq
  exact byteEq.trans (beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked c hc) i (List.mem_range.mpr hi)))

theorem code_image (base : BitVec 64) {c : Nat × Nat}
    (member : c ∈ Lean_D234_SecpCmul_c29E17.codeVAs) (i : Nat) (hi : i < 4) :
    referenceImageI SecpArtifact.elf base (fun _ => 0) (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) :=
  Lean_D234_SecpCmul_c29E17.code_image _ image_binds code_binds base _ member i hi

#print axioms image_binds
#print axioms scoped_image
#print axioms code_binds
#print axioms code_image
end PipeLean_D234_SecpCmul_c29.ImageBinding
