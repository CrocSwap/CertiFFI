import PipeLean_D234_SecpNeg_c11.Plan
import ArmCertPipe.ReturnValues
import ArmCertPipe.GPrefix
import ArmCertValue.PhysicalPairData
import ArmCertValue.PhysicalPairDataG
open Sail ArmFull ArmBridge.Draft
open ArmCertValue HeapV2StepCerts.RegBind
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 150000
namespace PipeLean_D234_SecpNeg_c11.PairData

theorem memory_prefix_0 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 0)).map (fun q => q.2.regs (.x 1)) =
      some (some (totalL rs_c00 + 1)) := rfl

theorem memory_base_0 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 0 x) : regVal x (.x 1) = inputs.getD (totalL rs_c00 + 1) 0 := by
  have whole : ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    rw [length]; exact compiles_D_c00 tp
  have current : (ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      ((plan_c00 tp).take 0)).map (fun q => q.2.regs (.x 1)) =
        some (some (totalL rs_c00 + 1)) := by
    rw [length]; exact memory_prefix_0 tp
  have same := ArmCertPipe.G.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c00 + 1) < inputs.length := by
    rw [length]; change totalL rs_c00 + 1 < totalL rs_c00 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_0

theorem load_tracked_0 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 0)).map (fun q =>
        (List.range 16).all (fun i => (q.2.memB O (8 * 0 + i)).isSome)) = some true := rfl

theorem load_payload_0 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 0 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x O (8 * 0 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix_g view regions_c00 σ0_c00 inputs
    (plan_c00 tp) 0 x O 0 agreement
  rw [length]; exact load_tracked_0 tp
#print axioms load_payload_0

theorem memory_prefix_2 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 2)).map (fun q => q.2.regs (.x 1)) =
      some (some (totalL rs_c00 + 1)) := rfl

theorem memory_base_2 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 2 x) : regVal x (.x 1) = inputs.getD (totalL rs_c00 + 1) 0 := by
  have whole : ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    rw [length]; exact compiles_D_c00 tp
  have current : (ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      ((plan_c00 tp).take 2)).map (fun q => q.2.regs (.x 1)) =
        some (some (totalL rs_c00 + 1)) := by
    rw [length]; exact memory_prefix_2 tp
  have same := ArmCertPipe.G.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c00 + 1) < inputs.length := by
    rw [length]; change totalL rs_c00 + 1 < totalL rs_c00 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_2

theorem load_tracked_2 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 2)).map (fun q =>
        (List.range 16).all (fun i => (q.2.memB O (8 * 2 + i)).isSome)) = some true := rfl

theorem load_payload_2 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 2 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x O (8 * 2 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix_g view regions_c00 σ0_c00 inputs
    (plan_c00 tp) 2 x O 2 agreement
  rw [length]; exact load_tracked_2 tp
#print axioms load_payload_2

theorem memory_prefix_14 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 14)).map (fun q => q.2.regs (.x 0)) =
      some (some (totalL rs_c00 + 0)) := rfl

theorem memory_base_14 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 14 x) : regVal x (.x 0) = inputs.getD (totalL rs_c00 + 0) 0 := by
  have whole : ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    rw [length]; exact compiles_D_c00 tp
  have current : (ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      ((plan_c00 tp).take 14)).map (fun q => q.2.regs (.x 0)) =
        some (some (totalL rs_c00 + 0)) := by
    rw [length]; exact memory_prefix_14 tp
  have same := ArmCertPipe.G.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c00 + 0) < inputs.length := by
    rw [length]; change totalL rs_c00 + 0 < totalL rs_c00 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_14

theorem memory_prefix_15 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 15)).map (fun q => q.2.regs (.x 0)) =
      some (some (totalL rs_c00 + 0)) := rfl

theorem memory_base_15 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 15 x) : regVal x (.x 0) = inputs.getD (totalL rs_c00 + 0) 0 := by
  have whole : ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    rw [length]; exact compiles_D_c00 tp
  have current : (ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      ((plan_c00 tp).take 15)).map (fun q => q.2.regs (.x 0)) =
        some (some (totalL rs_c00 + 0)) := by
    rw [length]; exact memory_prefix_15 tp
  have same := ArmCertPipe.G.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c00 + 0) < inputs.length := by
    rw [length]; change totalL rs_c00 + 0 < totalL rs_c00 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_15

end PipeLean_D234_SecpNeg_c11.PairData
