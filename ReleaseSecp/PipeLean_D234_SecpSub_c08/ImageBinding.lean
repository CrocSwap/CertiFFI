import Lean_D234_SecpSub_c08E17.Fetch
import SecpArtifact.Elf
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PipeLean_D234_SecpSub_c08.ImageBinding
open ArmCert.Translate.Model.StaticPie

theorem image_binds : Binds SecpArtifact.elf Lean_D234_SecpSub_c08Scoped.slices := SecpArtifact.sub_binds
theorem scoped_image : ScopedAdmitted SecpArtifact.elf Lean_D234_SecpSub_c08Scoped.closure Lean_D234_SecpSub_c08Scoped.slices.rela :=
  Lean_D234_SecpSub_c08Scoped.lean_d234_secpsub_c08_scoped _ image_binds

private def words : List (Nat × Nat) := [(5784, 2839549989), (5788, 2839546948), (5792, 3942908069), (5796, 4194500806), (5800, 2839617575), (5804, 2839612484), (5808, 4194566375), (5812, 4194500872), (5816, 3531635236), (5820, 2992636035), (5824, 2594123875), (5828, 3942842533), (5832, 4196335814), (5836, 4196335847), (5840, 3659464968), (5844, 2835355653), (5848, 2835423239), (5852, 3596551104)]
private theorem words_match : Lean_D234_SecpSub_c08E17.codeVAs = words := by rfl

private def fileBytes : List Nat := [37, 24, 64, 169, 68, 12, 64, 169, 165, 0, 4, 235, 198, 0, 3, 250, 39, 32, 65, 169, 68, 12, 65, 169, 231, 0, 4, 250, 8, 1, 3, 250, 36, 122, 128, 210, 131, 0, 96, 178, 99, 48, 159, 154, 165, 0, 3, 235, 198, 0, 31, 250, 231, 0, 31, 250, 8, 1, 31, 218, 5, 24, 0, 169, 7, 32, 1, 169, 192, 3, 95, 214]
private theorem file_slice :
    (SecpArtifact.elf.toList.drop 1688).take 72 = fileBytes := by rfl

private theorem slice_byte (bytes : Array Nat) (start size i : Nat) (data : List Nat)
    (bound : i < size) (binding : (bytes.toList.drop start).take size = data) :
    byte bytes (start + i) = data.getD i 0 := by
  rw [← binding]
  simp only [byte, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt bound, List.getElem?_drop, Array.getElem?_toList]

private theorem ranges :
    words.all (fun c => decide (5784 ≤ c.1 ∧ c.1 + 4 ≤ 5856)) = true := by decide

private def wordOK (c : Nat × Nat) : Bool :=
  (List.range 4).all fun i =>
    fileBytes.getD (c.1 - 5784 + i) 0 == (c.2 >>> (8 * i)) % 256

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
private theorem chunk_16 : ((words.drop 16).take 2).all wordOK = true := by rfl
private theorem end_check : (words.drop 18).all wordOK = true := by rfl

private theorem words_checked : words.all wordOK = true := by
  change (words.drop 0).all wordOK = true
  refine join _ 0 8 chunk_0 ?_
  refine join _ 8 8 chunk_8 ?_
  refine join _ 16 2 chunk_16 ?_
  exact end_check

theorem code_binds : Lean_D234_SecpSub_c08E17.CodeBinds SecpArtifact.elf := by
  intro c hc i hi
  rw [words_match] at hc
  have range := of_decide_eq_true (List.all_eq_true.mp ranges c hc)
  have bound : c.1 - 5784 + i < 72 := by omega
  have byteEq := slice_byte SecpArtifact.elf 1688 72
    (c.1 - 5784 + i) fileBytes bound file_slice
  have position : 1688 + (c.1 - 5784 + i) = 1592 + (c.1 - 5688) + i := by omega
  rw [position] at byteEq
  exact byteEq.trans (beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked c hc) i (List.mem_range.mpr hi)))

theorem code_image (base : BitVec 64) {c : Nat × Nat}
    (member : c ∈ Lean_D234_SecpSub_c08E17.codeVAs) (i : Nat) (hi : i < 4) :
    referenceImageI SecpArtifact.elf base (fun _ => 0) (c.1 + i) = some ((BitVec.ofNat 32 c.2).extractLsb' (8 * i) 8) :=
  Lean_D234_SecpSub_c08E17.code_image _ image_binds code_binds base _ member i hi

#print axioms image_binds
#print axioms scoped_image
#print axioms code_binds
#print axioms code_image
end PipeLean_D234_SecpSub_c08.ImageBinding
