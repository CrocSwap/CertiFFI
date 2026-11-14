import Lean_D234_SecpMod4_c30E17.Fetch
import SecpArtifact.Elf
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpMod4_c30.ImageBinding
open ArmCert.Translate.Model.StaticPie

theorem image_binds : Binds SecpArtifact.elf Lean_D234_SecpMod4_c30Scoped.slices := SecpArtifact.sub_binds
theorem scoped_image : ScopedAdmitted SecpArtifact.elf Lean_D234_SecpMod4_c30Scoped.closure Lean_D234_SecpMod4_c30Scoped.slices.rela :=
  Lean_D234_SecpMod4_c30Scoped.lean_d234_secpmod4_c30_scoped _ image_binds

private def words : List (Nat × Nat) := [(8032, 2839546914), (8036, 2839614500), (8040, 2315518054), (8044, 2315583686), (8048, 3531635239), (8052, 2992636135), (8056, 2869035239), (8060, 3122593990), (8064, 2592550978), (8068, 2592485475), (8072, 2592485508), (8076, 2592485541), (8080, 2835352578), (8084, 2835420164), (8088, 3596551104)]
private theorem words_match : Lean_D234_SecpMod4_c30E17.codeVAs = words := by rfl

private def fileBytes : List Nat := [34, 12, 64, 169, 36, 20, 65, 169, 102, 0, 4, 138, 198, 0, 5, 138, 39, 122, 128, 210, 231, 0, 96, 178, 231, 0, 2, 171, 198, 0, 31, 186, 66, 48, 135, 154, 99, 48, 134, 154, 132, 48, 134, 154, 165, 48, 134, 154, 2, 12, 0, 169, 4, 20, 1, 169, 192, 3, 95, 214]
private theorem file_slice :
    (SecpArtifact.elf.toList.drop 3936).take 60 = fileBytes := by rfl

private theorem slice_byte (bytes : Array Nat) (start size i : Nat) (data : List Nat)
    (bound : i < size) (binding : (bytes.toList.drop start).take size = data) :
    byte bytes (start + i) = data.getD i 0 := by
  rw [← binding]
  simp only [byte, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt bound, List.getElem?_drop, Array.getElem?_toList]

private theorem ranges :
    words.all (fun c => decide (8032 ≤ c.1 ∧ c.1 + 4 ≤ 8092)) = true := by decide

private def wordOK (c : Nat × Nat) : Bool :=
  (List.range 4).all fun i =>
    fileBytes.getD (c.1 - 8032 + i) 0 == (c.2 >>> (8 * i)) % 256

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
private theorem chunk_8 : ((words.drop 8).take 7).all wordOK = true := by rfl
private theorem end_check : (words.drop 15).all wordOK = true := by rfl

private theorem words_checked : words.all wordOK = true := by
  change (words.drop 0).all wordOK = true
  refine join _ 0 8 chunk_0 ?_
  refine join _ 8 7 chunk_8 ?_
  exact end_check

theorem code_binds : Lean_D234_SecpMod4_c30E17.CodeBinds SecpArtifact.elf := by
  intro c hc i hi
  rw [words_match] at hc
  have range := of_decide_eq_true (List.all_eq_true.mp ranges c hc)
  have bound : c.1 - 8032 + i < 60 := by omega
  have byteEq := slice_byte SecpArtifact.elf 3936 60
    (c.1 - 8032 + i) fileBytes bound file_slice
  have position : 3936 + (c.1 - 8032 + i) = 1592 + (c.1 - 5688) + i := by omega
  rw [position] at byteEq
  exact byteEq.trans (beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked c hc) i (List.mem_range.mpr hi)))

theorem code_image (base : BitVec 64) {c : Nat × Nat}
    (member : c ∈ Lean_D234_SecpMod4_c30E17.codeVAs) (i : Nat) (hi : i < 4) :
    referenceImageI SecpArtifact.elf base (fun _ => 0) (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) :=
  Lean_D234_SecpMod4_c30E17.code_image _ image_binds code_binds base _ member i hi

#print axioms image_binds
#print axioms scoped_image
#print axioms code_binds
#print axioms code_image
end PipeLean_D234_SecpMod4_c30.ImageBinding
