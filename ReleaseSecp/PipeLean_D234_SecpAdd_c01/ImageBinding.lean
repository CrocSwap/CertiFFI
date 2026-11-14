import Lean_D234_SecpAdd_c01E17.Fetch
import SecpArtifact.Elf
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpAdd_c01.ImageBinding
open ArmCert.Translate.Model.StaticPie

theorem image_binds : Binds SecpArtifact.elf Lean_D234_SecpAdd_c01Scoped.slices := SecpArtifact.sub_binds
theorem scoped_image : ScopedAdmitted SecpArtifact.elf Lean_D234_SecpAdd_c01Scoped.closure Lean_D234_SecpAdd_c01Scoped.slices.rela :=
  Lean_D234_SecpAdd_c01Scoped.lean_d234_secpadd_c01_scoped _ image_binds

private def words : List (Nat × Nat) := [(5688, 2839549989), (5692, 2839546948), (5696, 2869166245), (5700, 3120758982), (5704, 2839617575), (5708, 2839612484), (5712, 3120824551), (5716, 2315714761), (5720, 3120759048), (5724, 2315780393), (5728, 2585723875), (5732, 3531635236), (5736, 2992636036), (5740, 2869166271), (5744, 3122594111), (5748, 3122593891), (5752, 2594115716), (5756, 2869166245), (5760, 3122593990), (5764, 3122594023), (5768, 2585723144), (5772, 2835355653), (5776, 2835423239), (5780, 3596551104)]
private theorem words_match : Lean_D234_SecpAdd_c01E17.codeVAs = words := by rfl

private def fileBytes : List Nat := [37, 24, 64, 169, 68, 12, 64, 169, 165, 0, 4, 171, 198, 0, 3, 186, 39, 32, 65, 169, 68, 12, 65, 169, 231, 0, 4, 186, 201, 0, 7, 138, 8, 1, 3, 186, 41, 1, 8, 138, 227, 3, 31, 154, 36, 122, 128, 210, 132, 0, 96, 178, 191, 0, 4, 171, 63, 1, 31, 186, 99, 0, 31, 186, 132, 16, 159, 154, 165, 0, 4, 171, 198, 0, 31, 186, 231, 0, 31, 186, 8, 1, 31, 154, 5, 24, 0, 169, 7, 32, 1, 169, 192, 3, 95, 214]
private theorem file_slice :
    (SecpArtifact.elf.toList.drop 1592).take 96 = fileBytes := by rfl

private theorem slice_byte (bytes : Array Nat) (start size i : Nat) (data : List Nat)
    (bound : i < size) (binding : (bytes.toList.drop start).take size = data) :
    byte bytes (start + i) = data.getD i 0 := by
  rw [← binding]
  simp only [byte, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt bound, List.getElem?_drop, Array.getElem?_toList]

private theorem ranges :
    words.all (fun c => decide (5688 ≤ c.1 ∧ c.1 + 4 ≤ 5784)) = true := by decide

private def wordOK (c : Nat × Nat) : Bool :=
  (List.range 4).all fun i =>
    fileBytes.getD (c.1 - 5688 + i) 0 == (c.2 >>> (8 * i)) % 256

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
private theorem end_check : (words.drop 24).all wordOK = true := by rfl

private theorem words_checked : words.all wordOK = true := by
  change (words.drop 0).all wordOK = true
  refine join _ 0 8 chunk_0 ?_
  refine join _ 8 8 chunk_8 ?_
  refine join _ 16 8 chunk_16 ?_
  exact end_check

theorem code_binds : Lean_D234_SecpAdd_c01E17.CodeBinds SecpArtifact.elf := by
  intro c hc i hi
  rw [words_match] at hc
  have range := of_decide_eq_true (List.all_eq_true.mp ranges c hc)
  have bound : c.1 - 5688 + i < 96 := by omega
  have byteEq := slice_byte SecpArtifact.elf 1592 96
    (c.1 - 5688 + i) fileBytes bound file_slice
  have position : 1592 + (c.1 - 5688 + i) = 1592 + (c.1 - 5688) + i := by omega
  rw [position] at byteEq
  exact byteEq.trans (beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked c hc) i (List.mem_range.mpr hi)))

theorem code_image (base : BitVec 64) {c : Nat × Nat}
    (member : c ∈ Lean_D234_SecpAdd_c01E17.codeVAs) (i : Nat) (hi : i < 4) :
    referenceImageI SecpArtifact.elf base (fun _ => 0) (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) :=
  Lean_D234_SecpAdd_c01E17.code_image _ image_binds code_binds base _ member i hi

#print axioms image_binds
#print axioms scoped_image
#print axioms code_binds
#print axioms code_image
end PipeLean_D234_SecpAdd_c01.ImageBinding
