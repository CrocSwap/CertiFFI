import PipeLean_D234_SecpSub_c06.Plan
import ArmCertPipe.ReturnValues
import ArmCertPipe.FPrefix
import ArmCertValue.PhysicalPairData
open Sail ArmFull ArmBridge.Draft
open ArmCertValue HeapV2StepCerts.RegBind
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 150000
namespace PipeLean_D234_SecpSub_c06.PairData

theorem memory_prefix_0 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06
      ((plan_c06 tp).take 0)).map (fun q => q.2.regs (.x 1)) =
      some (some (totalL rs_c06 + 1)) := rfl

theorem memory_base_0 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 0 x) : regVal x (.x 1) = inputs.getD (totalL rs_c06 + 1) 0 := by
  have whole : ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length
      (plan_c06 tp) = some (D_c06 tp, finalSym_c06 tp) := by
    rw [length]; exact compiles_D_c06 tp
  have current : (ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length
      ((plan_c06 tp).take 0)).map (fun q => q.2.regs (.x 1)) =
        some (some (totalL rs_c06 + 1)) := by
    rw [length]; exact memory_prefix_0 tp
  have same := ArmCertPipe.F.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c06 + 1) < inputs.length := by
    rw [length]; change totalL rs_c06 + 1 < totalL rs_c06 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_0

theorem load_tracked_0 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06
      ((plan_c06 tp).take 0)).map (fun q =>
        (List.range 16).all (fun i => (q.2.memB X (8 * 0 + i)).isSome)) = some true := rfl

theorem load_payload_0 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 0 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x X (8 * 0 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix view regions_c06 σ0_c06 inputs
    (plan_c06 tp) 0 x X 0 agreement
  rw [length]; exact load_tracked_0 tp
#print axioms load_payload_0

theorem memory_prefix_1 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06
      ((plan_c06 tp).take 1)).map (fun q => q.2.regs (.x 2)) =
      some (some (totalL rs_c06 + 2)) := rfl

theorem memory_base_1 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 1 x) : regVal x (.x 2) = inputs.getD (totalL rs_c06 + 2) 0 := by
  have whole : ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length
      (plan_c06 tp) = some (D_c06 tp, finalSym_c06 tp) := by
    rw [length]; exact compiles_D_c06 tp
  have current : (ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length
      ((plan_c06 tp).take 1)).map (fun q => q.2.regs (.x 2)) =
        some (some (totalL rs_c06 + 2)) := by
    rw [length]; exact memory_prefix_1 tp
  have same := ArmCertPipe.F.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c06 + 2) < inputs.length := by
    rw [length]; change totalL rs_c06 + 2 < totalL rs_c06 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_1

theorem load_tracked_1 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06
      ((plan_c06 tp).take 1)).map (fun q =>
        (List.range 16).all (fun i => (q.2.memB X (8 * 0 + i)).isSome)) = some true := rfl

theorem load_payload_1 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 1 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x X (8 * 0 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix view regions_c06 σ0_c06 inputs
    (plan_c06 tp) 1 x X 0 agreement
  rw [length]; exact load_tracked_1 tp
#print axioms load_payload_1

theorem memory_prefix_4 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06
      ((plan_c06 tp).take 4)).map (fun q => q.2.regs (.x 1)) =
      some (some (totalL rs_c06 + 1)) := rfl

theorem memory_base_4 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 4 x) : regVal x (.x 1) = inputs.getD (totalL rs_c06 + 1) 0 := by
  have whole : ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length
      (plan_c06 tp) = some (D_c06 tp, finalSym_c06 tp) := by
    rw [length]; exact compiles_D_c06 tp
  have current : (ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length
      ((plan_c06 tp).take 4)).map (fun q => q.2.regs (.x 1)) =
        some (some (totalL rs_c06 + 1)) := by
    rw [length]; exact memory_prefix_4 tp
  have same := ArmCertPipe.F.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c06 + 1) < inputs.length := by
    rw [length]; change totalL rs_c06 + 1 < totalL rs_c06 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_4

theorem load_tracked_4 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06
      ((plan_c06 tp).take 4)).map (fun q =>
        (List.range 16).all (fun i => (q.2.memB X (8 * 2 + i)).isSome)) = some true := rfl

theorem load_payload_4 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 4 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x X (8 * 2 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix view regions_c06 σ0_c06 inputs
    (plan_c06 tp) 4 x X 2 agreement
  rw [length]; exact load_tracked_4 tp
#print axioms load_payload_4

theorem memory_prefix_5 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06
      ((plan_c06 tp).take 5)).map (fun q => q.2.regs (.x 2)) =
      some (some (totalL rs_c06 + 2)) := rfl

theorem memory_base_5 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 5 x) : regVal x (.x 2) = inputs.getD (totalL rs_c06 + 2) 0 := by
  have whole : ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length
      (plan_c06 tp) = some (D_c06 tp, finalSym_c06 tp) := by
    rw [length]; exact compiles_D_c06 tp
  have current : (ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length
      ((plan_c06 tp).take 5)).map (fun q => q.2.regs (.x 2)) =
        some (some (totalL rs_c06 + 2)) := by
    rw [length]; exact memory_prefix_5 tp
  have same := ArmCertPipe.F.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c06 + 2) < inputs.length := by
    rw [length]; change totalL rs_c06 + 2 < totalL rs_c06 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_5

theorem load_tracked_5 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06
      ((plan_c06 tp).take 5)).map (fun q =>
        (List.range 16).all (fun i => (q.2.memB X (8 * 2 + i)).isSome)) = some true := rfl

theorem load_payload_5 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 5 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x X (8 * 2 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix view regions_c06 σ0_c06 inputs
    (plan_c06 tp) 5 x X 2 agreement
  rw [length]; exact load_tracked_5 tp
#print axioms load_payload_5

theorem memory_prefix_15 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06
      ((plan_c06 tp).take 15)).map (fun q => q.2.regs (.x 0)) =
      some (some (totalL rs_c06 + 0)) := rfl

theorem memory_base_15 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 15 x) : regVal x (.x 0) = inputs.getD (totalL rs_c06 + 0) 0 := by
  have whole : ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length
      (plan_c06 tp) = some (D_c06 tp, finalSym_c06 tp) := by
    rw [length]; exact compiles_D_c06 tp
  have current : (ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length
      ((plan_c06 tp).take 15)).map (fun q => q.2.regs (.x 0)) =
        some (some (totalL rs_c06 + 0)) := by
    rw [length]; exact memory_prefix_15 tp
  have same := ArmCertPipe.F.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c06 + 0) < inputs.length := by
    rw [length]; change totalL rs_c06 + 0 < totalL rs_c06 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_15

theorem memory_prefix_16 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06
      ((plan_c06 tp).take 16)).map (fun q => q.2.regs (.x 0)) =
      some (some (totalL rs_c06 + 0)) := rfl

theorem memory_base_16 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 16 x) : regVal x (.x 0) = inputs.getD (totalL rs_c06 + 0) 0 := by
  have whole : ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length
      (plan_c06 tp) = some (D_c06 tp, finalSym_c06 tp) := by
    rw [length]; exact compiles_D_c06 tp
  have current : (ArmCertValue.F.compileRun regions_c06 σ0_c06 inputs.length
      ((plan_c06 tp).take 16)).map (fun q => q.2.regs (.x 0)) =
        some (some (totalL rs_c06 + 0)) := by
    rw [length]; exact memory_prefix_16 tp
  have same := ArmCertPipe.F.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c06 + 0) < inputs.length := by
    rw [length]; change totalL rs_c06 + 0 < totalL rs_c06 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_16

end PipeLean_D234_SecpSub_c06.PairData
