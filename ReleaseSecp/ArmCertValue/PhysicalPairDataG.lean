import ArmCertValue.PhysicalPairData
import ArmCertPipe.GPrefix

set_option autoImplicit false
set_option maxHeartbeats 150000

namespace ArmCertValue.PhysicalPairData
open ArmCertValue.Physical HeapV2StepCerts.RegBind

theorem pair_of_prefix_g (view : BytePA) (regions : List Region) (σ0 : Sym)
    (inputs : List (BitVec 64)) (plan : List ArmCertValue.G.Step) (k : Nat) (x : St)
    (r : Region) (word : Nat)
    (agreement : ArmCertPipe.G.AgreesAt view regions σ0 inputs plan k x)
    (checked : (ArmCertValue.G.compileRun regions σ0 inputs.length (plan.take k)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB r (8 * word + i)).isSome)) = some true) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      Physical.regionByte view x r (8 * word + i) = some (data.extractLsb' (8 * i) 8) := by
  obtain ⟨defs, σ, compiled, agrees, bounded⟩ := agreement
  rw [compiled] at checked
  simp only [Option.map_some, Option.some.injEq] at checked
  apply pair_of_agrees view (extend inputs defs) σ x agrees r word
  intro i bound
  exact List.all_eq_true.mp checked i (List.mem_range.mpr bound)

#print axioms pair_of_prefix_g
end ArmCertValue.PhysicalPairData
