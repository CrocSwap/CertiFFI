import TranslateSpan.SecpCurrentEntry
import SecpMath.SubSSA
import XlateMath236.PhysicalOutput

open Sail ArmFull ArmBridge.Draft ArmCertValue TranslateSpan
open XlateMath236.PhysicalOutput
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 2048

namespace ReleaseProfile.SecpInputTransport

-- Only tracked memory bytes agree. Register input slots, including LR and SP,
-- are deliberately outside this contract.
theorem snapshot_at (regions : List (Region × Nat))
    (leftView rightView : Physical.BytePA) (left right : NativeState) :
    (∀ r n, (r,n) ∈ regions → ∀ i < n,
      Physical.regionByte leftView left r i = Physical.regionByte rightView right r i) →
    ∀ i, Physical.Entry.snapshot leftView left regions i =
      Physical.Entry.snapshot rightView right regions i := by
  induction regions with
  | nil => intro _ _; rfl
  | cons item rest ih =>
    rcases item with ⟨r,n⟩
    intro bytes i
    by_cases inside : i < n
    · simp only [Physical.Entry.snapshot,ite_eq_left inside]
      rw [bytes r n List.mem_cons_self i inside]
    · simp only [Physical.Entry.snapshot,ite_eq_right inside]
      exact ih (fun r n member i bound => bytes r n (List.mem_cons_of_mem _ member) i bound) _

theorem inputs_prefix (regions : List (Region × Nat))
    (leftView rightView : Physical.BytePA) (left right : NativeState)
    (bytes : ∀ r n, (r,n) ∈ regions → ∀ i < n,
      Physical.regionByte leftView left r i = Physical.regionByte rightView right r i)
    (i : Nat) (inside : i < totalL regions) :
    (mkInputsL left regions (Physical.Entry.snapshot leftView left regions)).getD i 0 =
      (mkInputsL right regions (Physical.Entry.snapshot rightView right regions)).getD i 0 := by
  unfold mkInputsL
  rw [mkInputsG_getD left (totalL regions) _ i (by omega),
    mkInputsG_getD right (totalL regions) _ i (by omega)]
  simp only [inputValG,ite_eq_left inside]
  rw [snapshot_at regions leftView rightView left right bytes i]

theorem input_word {earlier final : List (BitVec 64)} {bound start : Nat}
    (same : ∀ i < bound, earlier.getD i 0 = final.getD i 0)
    (inside : start + 8 ≤ bound) :
    SecpMath.SubSSA.inputWord earlier start = SecpMath.SubSSA.inputWord final start :=
  SecpMath.TableEval.def_eval_same bound same _
    (SecpMath.SubSSA.inputWordDef_below start bound inside)

-- Scalar seam from 3b095 draft, using the existing actual GPR-input
-- readback theorem. Memory-prefix equality alone does not preserve this slot.
theorem input_gpr (p : SecpRawDeployment.Plan) (mapping : BitVec 64 → Option Nat)
    (left right : NativeState) (pin : Fin 31)
    (kept : left.regs.gpr[pin.val] = right.regs.gpr[pin.val]) :
    (SecpCurrentEntry.inputs p mapping left).getD (totalL p.regions + pin.val) 0 =
      (SecpCurrentEntry.inputs p mapping right).getD (totalL p.regions + pin.val) 0 := by
  rw [SecpCurrentEntry.inputs_gpr p mapping left pin.val pin.isLt,
    SecpCurrentEntry.inputs_gpr p mapping right pin.val pin.isLt]
  simp only [SecpRawDeployment.entryGPR,dite_eq_left pin.isLt]
  exact kept

theorem input_limbs {earlier final : List (BitVec 64)} {bound start : Nat}
    (same : ∀ i < bound, earlier.getD i 0 = final.getD i 0)
    (inside : start + 32 ≤ bound) :
    SecpMath.SubSSA.inputLimbs earlier start = SecpMath.SubSSA.inputLimbs final start := by
  unfold SecpMath.SubSSA.inputLimbs
  rw [input_word (start := start) same (by omega),
    input_word (start := start+8) same (by omega),
    input_word (start := start+16) same (by omega),
    input_word (start := start+24) same (by omega)]

theorem output_bytes (leftView rightView : Physical.BytePA) (left right : NativeState)
    (region : Region) (view : ∀ i < 32, leftView region i = rightView region i)
    (memory : ∀ pa : Nat, left.mem[pa]? = right.mem[pa]?) :
    physicalBytes leftView left region = physicalBytes rightView right region := by
  apply List.map_congr_left
  intro i member
  unfold Physical.regionByte
  rw [view i (List.mem_range.mp member)]
  cases rightView region i with
  | none => rfl
  | some pa => exact memory pa

#print axioms snapshot_at
#print axioms inputs_prefix
#print axioms input_word
#print axioms input_gpr
#print axioms input_limbs
#print axioms output_bytes
end ReleaseProfile.SecpInputTransport
