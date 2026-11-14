import Lean_D234_SecpNeg_c11E17.Fetch
import SecpArtifact.Elf
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpNeg_c11.ImageBinding
open ArmCert.Translate.Model.StaticPie

theorem image_binds : Binds SecpArtifact.elf Lean_D234_SecpNeg_c11Scoped.slices := SecpArtifact.sub_binds
theorem scoped_image : ScopedAdmitted SecpArtifact.elf Lean_D234_SecpNeg_c11Scoped.closure Lean_D234_SecpNeg_c11Scoped.slices.rela :=
  Lean_D234_SecpNeg_c11Scoped.lean_d234_secpneg_c11_scoped _ image_binds

private def words : List (Nat × Nat) := [(5856, 2839547939), (5860, 2852388967), (5864, 2839615525), (5868, 2852454631), (5872, 2852520167), (5876, 3944677631), (5880, 3667854306), (5884, 3531635207), (5888, 2992636135), (5892, 2317811783), (5896, 3942842595), (5900, 4194566212), (5904, 4194631749), (5908, 3657826374), (5912, 2835353603), (5916, 2835421189), (5920, 3596551104)]
private theorem words_match : Lean_D234_SecpNeg_c11E17.codeVAs = words := by rfl

private def fileBytes : List Nat := [35, 16, 64, 169, 103, 0, 4, 170, 37, 24, 65, 169, 231, 0, 5, 170, 231, 0, 6, 170, 255, 0, 31, 235, 226, 3, 159, 218, 7, 122, 128, 210, 231, 0, 96, 178, 71, 0, 39, 138, 227, 0, 3, 235, 68, 0, 4, 250, 69, 0, 5, 250, 70, 0, 6, 218, 3, 16, 0, 169, 5, 24, 1, 169, 192, 3, 95, 214]
private theorem file_slice :
    (SecpArtifact.elf.toList.drop 1760).take 68 = fileBytes := by rfl

private theorem slice_byte (bytes : Array Nat) (start size i : Nat) (data : List Nat)
    (bound : i < size) (binding : (bytes.toList.drop start).take size = data) :
    byte bytes (start + i) = data.getD i 0 := by
  rw [← binding]
  simp only [byte, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt bound, List.getElem?_drop, Array.getElem?_toList]

private theorem ranges :
    words.all (fun c => decide (5856 ≤ c.1 ∧ c.1 + 4 ≤ 5924)) = true := by decide

private def wordOK (c : Nat × Nat) : Bool :=
  (List.range 4).all fun i =>
    fileBytes.getD (c.1 - 5856 + i) 0 == (c.2 >>> (8 * i)) % 256

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
private theorem chunk_16 : ((words.drop 16).take 1).all wordOK = true := by rfl
private theorem end_check : (words.drop 17).all wordOK = true := by rfl

private theorem words_checked : words.all wordOK = true := by
  change (words.drop 0).all wordOK = true
  refine join _ 0 8 chunk_0 ?_
  refine join _ 8 8 chunk_8 ?_
  refine join _ 16 1 chunk_16 ?_
  exact end_check

theorem code_binds : Lean_D234_SecpNeg_c11E17.CodeBinds SecpArtifact.elf := by
  intro c hc i hi
  rw [words_match] at hc
  have range := of_decide_eq_true (List.all_eq_true.mp ranges c hc)
  have bound : c.1 - 5856 + i < 68 := by omega
  have byteEq := slice_byte SecpArtifact.elf 1760 68
    (c.1 - 5856 + i) fileBytes bound file_slice
  have position : 1760 + (c.1 - 5856 + i) = 1592 + (c.1 - 5688) + i := by omega
  rw [position] at byteEq
  exact byteEq.trans (beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked c hc) i (List.mem_range.mpr hi)))

theorem code_image (base : BitVec 64) {c : Nat × Nat}
    (member : c ∈ Lean_D234_SecpNeg_c11E17.codeVAs) (i : Nat) (hi : i < 4) :
    referenceImageI SecpArtifact.elf base (fun _ => 0) (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) :=
  Lean_D234_SecpNeg_c11E17.code_image _ image_binds code_binds base _ member i hi

#print axioms image_binds
#print axioms scoped_image
#print axioms code_binds
#print axioms code_image
end PipeLean_D234_SecpNeg_c11.ImageBinding
