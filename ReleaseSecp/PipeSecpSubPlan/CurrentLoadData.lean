-- GENERATED: actual current Sub load payloads from compiled prefixes.
import PipeSecpSubPlan.Inst
import ArmCertValue.PhysicalPairData
open Sail ArmFull ArmCertWalk ArmCert.Translate.Model
open ArmCertValue HeapV2StepCerts.RegBind
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000
namespace PipeSecpSubPlan
theorem load_tracked_c05_0 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c05 σ0_c05 n0_c05 ((plan_c05 tp).take 0)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB X (8 * 0 + i)).isSome)) = some true := rfl
theorem load_payload_c05_0 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c05) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c05 σ0_c05 inputs (plan_c05 tp) 0 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x X (8 * 0 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c05 σ0_c05 inputs (plan_c05 tp) 0 x X 0 agreement
  rw [hlen]; exact load_tracked_c05_0 tp
#print axioms load_tracked_c05_0
#print axioms load_payload_c05_0

theorem load_tracked_c05_1 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c05 σ0_c05 n0_c05 ((plan_c05 tp).take 1)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB Y (8 * 0 + i)).isSome)) = some true := rfl
theorem load_payload_c05_1 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c05) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c05 σ0_c05 inputs (plan_c05 tp) 1 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x Y (8 * 0 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c05 σ0_c05 inputs (plan_c05 tp) 1 x Y 0 agreement
  rw [hlen]; exact load_tracked_c05_1 tp
#print axioms load_tracked_c05_1
#print axioms load_payload_c05_1

theorem load_tracked_c05_4 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c05 σ0_c05 n0_c05 ((plan_c05 tp).take 4)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB X (8 * 2 + i)).isSome)) = some true := rfl
theorem load_payload_c05_4 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c05) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c05 σ0_c05 inputs (plan_c05 tp) 4 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x X (8 * 2 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c05 σ0_c05 inputs (plan_c05 tp) 4 x X 2 agreement
  rw [hlen]; exact load_tracked_c05_4 tp
#print axioms load_tracked_c05_4
#print axioms load_payload_c05_4

theorem load_tracked_c05_5 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c05 σ0_c05 n0_c05 ((plan_c05 tp).take 5)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB Y (8 * 2 + i)).isSome)) = some true := rfl
theorem load_payload_c05_5 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c05) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c05 σ0_c05 inputs (plan_c05 tp) 5 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x Y (8 * 2 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c05 σ0_c05 inputs (plan_c05 tp) 5 x Y 2 agreement
  rw [hlen]; exact load_tracked_c05_5 tp
#print axioms load_tracked_c05_5
#print axioms load_payload_c05_5

theorem load_tracked_c06_0 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06 ((plan_c06 tp).take 0)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB X (8 * 0 + i)).isSome)) = some true := rfl
theorem load_payload_c06_0 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 0 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x X (8 * 0 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c06 σ0_c06 inputs (plan_c06 tp) 0 x X 0 agreement
  rw [hlen]; exact load_tracked_c06_0 tp
#print axioms load_tracked_c06_0
#print axioms load_payload_c06_0

theorem load_tracked_c06_1 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06 ((plan_c06 tp).take 1)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB X (8 * 0 + i)).isSome)) = some true := rfl
theorem load_payload_c06_1 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 1 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x X (8 * 0 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c06 σ0_c06 inputs (plan_c06 tp) 1 x X 0 agreement
  rw [hlen]; exact load_tracked_c06_1 tp
#print axioms load_tracked_c06_1
#print axioms load_payload_c06_1

theorem load_tracked_c06_4 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06 ((plan_c06 tp).take 4)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB X (8 * 2 + i)).isSome)) = some true := rfl
theorem load_payload_c06_4 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 4 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x X (8 * 2 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c06 σ0_c06 inputs (plan_c06 tp) 4 x X 2 agreement
  rw [hlen]; exact load_tracked_c06_4 tp
#print axioms load_tracked_c06_4
#print axioms load_payload_c06_4

theorem load_tracked_c06_5 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c06 σ0_c06 n0_c06 ((plan_c06 tp).take 5)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB X (8 * 2 + i)).isSome)) = some true := rfl
theorem load_payload_c06_5 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c06) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c06 σ0_c06 inputs (plan_c06 tp) 5 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x X (8 * 2 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c06 σ0_c06 inputs (plan_c06 tp) 5 x X 2 agreement
  rw [hlen]; exact load_tracked_c06_5 tp
#print axioms load_tracked_c06_5
#print axioms load_payload_c06_5

theorem load_tracked_c07_0 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c07 σ0_c07 n0_c07 ((plan_c07 tp).take 0)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB O (8 * 0 + i)).isSome)) = some true := rfl
theorem load_payload_c07_0 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c07) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c07 σ0_c07 inputs (plan_c07 tp) 0 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x O (8 * 0 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c07 σ0_c07 inputs (plan_c07 tp) 0 x O 0 agreement
  rw [hlen]; exact load_tracked_c07_0 tp
#print axioms load_tracked_c07_0
#print axioms load_payload_c07_0

theorem load_tracked_c07_1 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c07 σ0_c07 n0_c07 ((plan_c07 tp).take 1)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB Y (8 * 0 + i)).isSome)) = some true := rfl
theorem load_payload_c07_1 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c07) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c07 σ0_c07 inputs (plan_c07 tp) 1 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x Y (8 * 0 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c07 σ0_c07 inputs (plan_c07 tp) 1 x Y 0 agreement
  rw [hlen]; exact load_tracked_c07_1 tp
#print axioms load_tracked_c07_1
#print axioms load_payload_c07_1

theorem load_tracked_c07_4 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c07 σ0_c07 n0_c07 ((plan_c07 tp).take 4)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB O (8 * 2 + i)).isSome)) = some true := rfl
theorem load_payload_c07_4 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c07) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c07 σ0_c07 inputs (plan_c07 tp) 4 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x O (8 * 2 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c07 σ0_c07 inputs (plan_c07 tp) 4 x O 2 agreement
  rw [hlen]; exact load_tracked_c07_4 tp
#print axioms load_tracked_c07_4
#print axioms load_payload_c07_4

theorem load_tracked_c07_5 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c07 σ0_c07 n0_c07 ((plan_c07 tp).take 5)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB Y (8 * 2 + i)).isSome)) = some true := rfl
theorem load_payload_c07_5 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c07) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c07 σ0_c07 inputs (plan_c07 tp) 5 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x Y (8 * 2 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c07 σ0_c07 inputs (plan_c07 tp) 5 x Y 2 agreement
  rw [hlen]; exact load_tracked_c07_5 tp
#print axioms load_tracked_c07_5
#print axioms load_payload_c07_5

theorem load_tracked_c08_0 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c08 σ0_c08 n0_c08 ((plan_c08 tp).take 0)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB X (8 * 0 + i)).isSome)) = some true := rfl
theorem load_payload_c08_0 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c08) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c08 σ0_c08 inputs (plan_c08 tp) 0 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x X (8 * 0 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c08 σ0_c08 inputs (plan_c08 tp) 0 x X 0 agreement
  rw [hlen]; exact load_tracked_c08_0 tp
#print axioms load_tracked_c08_0
#print axioms load_payload_c08_0

theorem load_tracked_c08_1 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c08 σ0_c08 n0_c08 ((plan_c08 tp).take 1)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB O (8 * 0 + i)).isSome)) = some true := rfl
theorem load_payload_c08_1 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c08) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c08 σ0_c08 inputs (plan_c08 tp) 1 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x O (8 * 0 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c08 σ0_c08 inputs (plan_c08 tp) 1 x O 0 agreement
  rw [hlen]; exact load_tracked_c08_1 tp
#print axioms load_tracked_c08_1
#print axioms load_payload_c08_1

theorem load_tracked_c08_4 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c08 σ0_c08 n0_c08 ((plan_c08 tp).take 4)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB X (8 * 2 + i)).isSome)) = some true := rfl
theorem load_payload_c08_4 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c08) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c08 σ0_c08 inputs (plan_c08 tp) 4 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x X (8 * 2 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c08 σ0_c08 inputs (plan_c08 tp) 4 x X 2 agreement
  rw [hlen]; exact load_tracked_c08_4 tp
#print axioms load_tracked_c08_4
#print axioms load_payload_c08_4

theorem load_tracked_c08_5 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c08 σ0_c08 n0_c08 ((plan_c08 tp).take 5)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB O (8 * 2 + i)).isSome)) = some true := rfl
theorem load_payload_c08_5 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c08) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c08 σ0_c08 inputs (plan_c08 tp) 5 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x O (8 * 2 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c08 σ0_c08 inputs (plan_c08 tp) 5 x O 2 agreement
  rw [hlen]; exact load_tracked_c08_5 tp
#print axioms load_tracked_c08_5
#print axioms load_payload_c08_5

theorem load_tracked_c09_0 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c09 σ0_c09 n0_c09 ((plan_c09 tp).take 0)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB O (8 * 0 + i)).isSome)) = some true := rfl
theorem load_payload_c09_0 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c09) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c09 σ0_c09 inputs (plan_c09 tp) 0 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x O (8 * 0 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c09 σ0_c09 inputs (plan_c09 tp) 0 x O 0 agreement
  rw [hlen]; exact load_tracked_c09_0 tp
#print axioms load_tracked_c09_0
#print axioms load_payload_c09_0

theorem load_tracked_c09_1 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c09 σ0_c09 n0_c09 ((plan_c09 tp).take 1)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB O (8 * 0 + i)).isSome)) = some true := rfl
theorem load_payload_c09_1 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c09) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c09 σ0_c09 inputs (plan_c09 tp) 1 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x O (8 * 0 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c09 σ0_c09 inputs (plan_c09 tp) 1 x O 0 agreement
  rw [hlen]; exact load_tracked_c09_1 tp
#print axioms load_tracked_c09_1
#print axioms load_payload_c09_1

theorem load_tracked_c09_4 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c09 σ0_c09 n0_c09 ((plan_c09 tp).take 4)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB O (8 * 2 + i)).isSome)) = some true := rfl
theorem load_payload_c09_4 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c09) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c09 σ0_c09 inputs (plan_c09 tp) 4 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x O (8 * 2 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c09 σ0_c09 inputs (plan_c09 tp) 4 x O 2 agreement
  rw [hlen]; exact load_tracked_c09_4 tp
#print axioms load_tracked_c09_4
#print axioms load_payload_c09_4

theorem load_tracked_c09_5 (tp : BitVec 64) :
    (ArmCertValue.F.compileRun regions_c09 σ0_c09 n0_c09 ((plan_c09 tp).take 5)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB O (8 * 2 + i)).isSome)) = some true := rfl
theorem load_payload_c09_5 (view : ArmCertValue.Physical.BytePA)
    (inputs : List (BitVec 64)) (tp : BitVec 64) (hlen : inputs.length = n0_c09) (x : St)
    (agreement : ArmCertPipe.F.AgreesAt view regions_c09 σ0_c09 inputs (plan_c09 tp) 5 x) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x O (8 * 2 + i) = some (data.extractLsb' (8 * i) 8) := by
  apply ArmCertValue.PhysicalPairData.pair_of_prefix view regions_c09 σ0_c09 inputs (plan_c09 tp) 5 x O 2 agreement
  rw [hlen]; exact load_tracked_c09_5 tp
#print axioms load_tracked_c09_5
#print axioms load_payload_c09_5

end PipeSecpSubPlan
