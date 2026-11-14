import Lean_D234_SecpDouble_c13E17.Fetch
import SecpArtifact.Elf
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpDouble_c13.ImageBinding
open ArmCert.Translate.Model.StaticPie

theorem image_binds : Binds SecpArtifact.elf Lean_D234_SecpDouble_c13Scoped.slices := SecpArtifact.sub_binds
theorem scoped_image : ScopedAdmitted SecpArtifact.elf Lean_D234_SecpDouble_c13Scoped.closure Lean_D234_SecpDouble_c13Scoped.slices.rela :=
  Lean_D234_SecpDouble_c13Scoped.lean_d234_secpdouble_c13_scoped _ image_binds

private def words : List (Nat × Nat) := [(5924, 2839614500), (5928, 3548380326), (5932, 2479160485), (5936, 2839546914), (5940, 2479094916), (5944, 2315583623), (5948, 2479029347), (5952, 2315452647), (5956, 3548379202), (5960, 3531635240), (5964, 2992636168), (5968, 2869428319), (5972, 3122594047), (5976, 3122593990), (5980, 2594115848), (5984, 2869428290), (5988, 3122593891), (5992, 3122593924), (5996, 2585723045), (6000, 2835352578), (6004, 2835420164), (6008, 3596551104)]
private theorem words_match : Lean_D234_SecpDouble_c13E17.codeVAs = words := by rfl

private def fileBytes : List Nat := [36, 20, 65, 169, 166, 252, 127, 211, 165, 252, 196, 147, 34, 12, 64, 169, 132, 252, 195, 147, 135, 0, 5, 138, 99, 252, 194, 147, 231, 0, 3, 138, 66, 248, 127, 211, 40, 122, 128, 210, 8, 1, 96, 178, 95, 0, 8, 171, 255, 0, 31, 186, 198, 0, 31, 186, 8, 17, 159, 154, 66, 0, 8, 171, 99, 0, 31, 186, 132, 0, 31, 186, 165, 0, 31, 154, 2, 12, 0, 169, 4, 20, 1, 169, 192, 3, 95, 214]
private theorem file_slice :
    (SecpArtifact.elf.toList.drop 1828).take 88 = fileBytes := by rfl

private theorem slice_byte (bytes : Array Nat) (start size i : Nat) (data : List Nat)
    (bound : i < size) (binding : (bytes.toList.drop start).take size = data) :
    byte bytes (start + i) = data.getD i 0 := by
  rw [← binding]
  simp only [byte, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt bound, List.getElem?_drop, Array.getElem?_toList]

private theorem ranges :
    words.all (fun c => decide (5924 ≤ c.1 ∧ c.1 + 4 ≤ 6012)) = true := by decide

private def wordOK (c : Nat × Nat) : Bool :=
  (List.range 4).all fun i =>
    fileBytes.getD (c.1 - 5924 + i) 0 == (c.2 >>> (8 * i)) % 256

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
private theorem chunk_16 : ((words.drop 16).take 6).all wordOK = true := by rfl
private theorem end_check : (words.drop 22).all wordOK = true := by rfl

private theorem words_checked : words.all wordOK = true := by
  change (words.drop 0).all wordOK = true
  refine join _ 0 8 chunk_0 ?_
  refine join _ 8 8 chunk_8 ?_
  refine join _ 16 6 chunk_16 ?_
  exact end_check

theorem code_binds : Lean_D234_SecpDouble_c13E17.CodeBinds SecpArtifact.elf := by
  intro c hc i hi
  rw [words_match] at hc
  have range := of_decide_eq_true (List.all_eq_true.mp ranges c hc)
  have bound : c.1 - 5924 + i < 88 := by omega
  have byteEq := slice_byte SecpArtifact.elf 1828 88
    (c.1 - 5924 + i) fileBytes bound file_slice
  have position : 1828 + (c.1 - 5924 + i) = 1592 + (c.1 - 5688) + i := by omega
  rw [position] at byteEq
  exact byteEq.trans (beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked c hc) i (List.mem_range.mpr hi)))

theorem code_image (base : BitVec 64) {c : Nat × Nat}
    (member : c ∈ Lean_D234_SecpDouble_c13E17.codeVAs) (i : Nat) (hi : i < 4) :
    referenceImageI SecpArtifact.elf base (fun _ => 0) (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) :=
  Lean_D234_SecpDouble_c13E17.code_image _ image_binds code_binds base _ member i hi

#print axioms image_binds
#print axioms scoped_image
#print axioms code_binds
#print axioms code_image
end PipeLean_D234_SecpDouble_c13.ImageBinding
