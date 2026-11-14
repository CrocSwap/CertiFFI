import PipeLean_D234_SecpMul_c14.Plan
import ArmCertPipe.ReturnValues
import ArmCertPipe.GPrefix
import ArmCertValue.PhysicalPairData
import ArmCertValue.PhysicalPairDataG
open Sail ArmFull ArmBridge.Draft
open ArmCertValue HeapV2StepCerts.RegBind
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 150000
namespace PipeLean_D234_SecpMul_c14.PairData

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
        (List.range 16).all (fun i => (q.2.memB X (8 * 0 + i)).isSome)) = some true := rfl

theorem load_payload_0 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 0 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x X (8 * 0 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix_g view regions_c00 σ0_c00 inputs
    (plan_c00 tp) 0 x X 0 agreement
  rw [length]; exact load_tracked_0 tp
#print axioms load_payload_0

theorem memory_prefix_1 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 1)).map (fun q => q.2.regs (.x 2)) =
      some (some (totalL rs_c00 + 2)) := rfl

theorem memory_base_1 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 1 x) : regVal x (.x 2) = inputs.getD (totalL rs_c00 + 2) 0 := by
  have whole : ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    rw [length]; exact compiles_D_c00 tp
  have current : (ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      ((plan_c00 tp).take 1)).map (fun q => q.2.regs (.x 2)) =
        some (some (totalL rs_c00 + 2)) := by
    rw [length]; exact memory_prefix_1 tp
  have same := ArmCertPipe.G.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c00 + 2) < inputs.length := by
    rw [length]; change totalL rs_c00 + 2 < totalL rs_c00 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_1

theorem load_tracked_1 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 1)).map (fun q =>
        (List.range 16).all (fun i => (q.2.memB Y (8 * 0 + i)).isSome)) = some true := rfl

theorem load_payload_1 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 1 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x Y (8 * 0 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix_g view regions_c00 σ0_c00 inputs
    (plan_c00 tp) 1 x Y 0 agreement
  rw [length]; exact load_tracked_1 tp
#print axioms load_payload_1

theorem memory_prefix_25 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 25)).map (fun q => q.2.regs (.x 1)) =
      some (some (totalL rs_c00 + 1)) := rfl

theorem memory_base_25 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 25 x) : regVal x (.x 1) = inputs.getD (totalL rs_c00 + 1) 0 := by
  have whole : ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    rw [length]; exact compiles_D_c00 tp
  have current : (ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      ((plan_c00 tp).take 25)).map (fun q => q.2.regs (.x 1)) =
        some (some (totalL rs_c00 + 1)) := by
    rw [length]; exact memory_prefix_25 tp
  have same := ArmCertPipe.G.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c00 + 1) < inputs.length := by
    rw [length]; change totalL rs_c00 + 1 < totalL rs_c00 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_25

theorem load_tracked_25 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 25)).map (fun q =>
        (List.range 16).all (fun i => (q.2.memB X (8 * 2 + i)).isSome)) = some true := rfl

theorem load_payload_25 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 25 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x X (8 * 2 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix_g view regions_c00 σ0_c00 inputs
    (plan_c00 tp) 25 x X 2 agreement
  rw [length]; exact load_tracked_25 tp
#print axioms load_payload_25

theorem memory_prefix_26 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 26)).map (fun q => q.2.regs (.x 2)) =
      some (some (totalL rs_c00 + 2)) := rfl

theorem memory_base_26 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 26 x) : regVal x (.x 2) = inputs.getD (totalL rs_c00 + 2) 0 := by
  have whole : ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    rw [length]; exact compiles_D_c00 tp
  have current : (ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      ((plan_c00 tp).take 26)).map (fun q => q.2.regs (.x 2)) =
        some (some (totalL rs_c00 + 2)) := by
    rw [length]; exact memory_prefix_26 tp
  have same := ArmCertPipe.G.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c00 + 2) < inputs.length := by
    rw [length]; change totalL rs_c00 + 2 < totalL rs_c00 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_26

theorem load_tracked_26 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 26)).map (fun q =>
        (List.range 16).all (fun i => (q.2.memB Y (8 * 2 + i)).isSome)) = some true := rfl

theorem load_payload_26 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 26 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x Y (8 * 2 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix_g view regions_c00 σ0_c00 inputs
    (plan_c00 tp) 26 x Y 2 agreement
  rw [length]; exact load_tracked_26 tp
#print axioms load_payload_26

theorem memory_prefix_50 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 50)).map (fun q => q.2.regs (.x 1)) =
      some (some (totalL rs_c00 + 1)) := rfl

theorem memory_base_50 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 50 x) : regVal x (.x 1) = inputs.getD (totalL rs_c00 + 1) 0 := by
  have whole : ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    rw [length]; exact compiles_D_c00 tp
  have current : (ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      ((plan_c00 tp).take 50)).map (fun q => q.2.regs (.x 1)) =
        some (some (totalL rs_c00 + 1)) := by
    rw [length]; exact memory_prefix_50 tp
  have same := ArmCertPipe.G.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c00 + 1) < inputs.length := by
    rw [length]; change totalL rs_c00 + 1 < totalL rs_c00 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_50

theorem load_tracked_50 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 50)).map (fun q =>
        (List.range 16).all (fun i => (q.2.memB X (8 * 2 + i)).isSome)) = some true := rfl

theorem load_payload_50 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 50 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x X (8 * 2 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix_g view regions_c00 σ0_c00 inputs
    (plan_c00 tp) 50 x X 2 agreement
  rw [length]; exact load_tracked_50 tp
#print axioms load_payload_50

theorem memory_prefix_51 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 51)).map (fun q => q.2.regs (.x 1)) =
      some (some (totalL rs_c00 + 1)) := rfl

theorem memory_base_51 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 51 x) : regVal x (.x 1) = inputs.getD (totalL rs_c00 + 1) 0 := by
  have whole : ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    rw [length]; exact compiles_D_c00 tp
  have current : (ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      ((plan_c00 tp).take 51)).map (fun q => q.2.regs (.x 1)) =
        some (some (totalL rs_c00 + 1)) := by
    rw [length]; exact memory_prefix_51 tp
  have same := ArmCertPipe.G.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c00 + 1) < inputs.length := by
    rw [length]; change totalL rs_c00 + 1 < totalL rs_c00 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_51

theorem load_tracked_51 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 51)).map (fun q =>
        (List.range 16).all (fun i => (q.2.memB X (8 * 0 + i)).isSome)) = some true := rfl

theorem load_payload_51 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 51 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x X (8 * 0 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix_g view regions_c00 σ0_c00 inputs
    (plan_c00 tp) 51 x X 0 agreement
  rw [length]; exact load_tracked_51 tp
#print axioms load_payload_51

theorem memory_prefix_55 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 55)).map (fun q => q.2.regs (.x 2)) =
      some (some (totalL rs_c00 + 2)) := rfl

theorem memory_base_55 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 55 x) : regVal x (.x 2) = inputs.getD (totalL rs_c00 + 2) 0 := by
  have whole : ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    rw [length]; exact compiles_D_c00 tp
  have current : (ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      ((plan_c00 tp).take 55)).map (fun q => q.2.regs (.x 2)) =
        some (some (totalL rs_c00 + 2)) := by
    rw [length]; exact memory_prefix_55 tp
  have same := ArmCertPipe.G.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c00 + 2) < inputs.length := by
    rw [length]; change totalL rs_c00 + 2 < totalL rs_c00 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_55

theorem load_tracked_55 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 55)).map (fun q =>
        (List.range 16).all (fun i => (q.2.memB Y (8 * 0 + i)).isSome)) = some true := rfl

theorem load_payload_55 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 55 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 → Physical.regionByte view x Y (8 * 0 + i) =
      some (data.extractLsb' (8 * i) 8) := by
  apply PhysicalPairData.pair_of_prefix_g view regions_c00 σ0_c00 inputs
    (plan_c00 tp) 55 x Y 0 agreement
  rw [length]; exact load_tracked_55 tp
#print axioms load_payload_55

theorem memory_prefix_155 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 155)).map (fun q => q.2.regs (.x 0)) =
      some (some (totalL rs_c00 + 0)) := rfl

theorem memory_base_155 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 155 x) : regVal x (.x 0) = inputs.getD (totalL rs_c00 + 0) 0 := by
  have whole : ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    rw [length]; exact compiles_D_c00 tp
  have current : (ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      ((plan_c00 tp).take 155)).map (fun q => q.2.regs (.x 0)) =
        some (some (totalL rs_c00 + 0)) := by
    rw [length]; exact memory_prefix_155 tp
  have same := ArmCertPipe.G.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c00 + 0) < inputs.length := by
    rw [length]; change totalL rs_c00 + 0 < totalL rs_c00 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_155

theorem memory_prefix_156 (tp : BitVec 64) :
    (ArmCertValue.G.compileRun regions_c00 σ0_c00 n0_c00
      ((plan_c00 tp).take 156)).map (fun q => q.2.regs (.x 0)) =
      some (some (totalL rs_c00 + 0)) := rfl

theorem memory_base_156 (view : Physical.BytePA) (inputs : List (BitVec 64))
    (tp : BitVec 64) (length : inputs.length = n0_c00) (x : St)
    (agreement : ArmCertPipe.G.AgreesAt view regions_c00 σ0_c00 inputs (plan_c00 tp) 156 x) : regVal x (.x 0) = inputs.getD (totalL rs_c00 + 0) 0 := by
  have whole : ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      (plan_c00 tp) = some (D_c00 tp, finalSym_c00 tp) := by
    rw [length]; exact compiles_D_c00 tp
  have current : (ArmCertValue.G.compileRun regions_c00 σ0_c00 inputs.length
      ((plan_c00 tp).take 156)).map (fun q => q.2.regs (.x 0)) =
        some (some (totalL rs_c00 + 0)) := by
    rw [length]; exact memory_prefix_156 tp
  have same := ArmCertPipe.G.regVal_of_agreesAt agreement whole current
  have bound : (totalL rs_c00 + 0) < inputs.length := by
    rw [length]; change totalL rs_c00 + 0 < totalL rs_c00 + 36; omega
  rw [ArmCertPipe.ReturnValues.input_prefix _ _ _ bound] at same
  exact same
#print axioms memory_base_156

end PipeLean_D234_SecpMul_c14.PairData
