-- Current tracked SSA bytes supply the actual pair - load payload.
import ArmCertValue.PhysicalLemmas
import ArmCertPipe.FPrefix
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace ArmCertValue.PhysicalPairData
open ArmCertValue ArmCertValue.Physical HeapV2StepCerts.RegBind
open ArmCertValue.MemRegion (byteOf byteOf_getLsbD)

theorem word_exists (view : BytePA) (x : St) (r : Region) (w : Nat)
    (present : ∀ i, i < 8 → (ArmCertValue.Physical.regionByte view x r (8 * w + i)).isSome = true) :
    ∃ v, ArmCertValue.Physical.regionWord view x r w = some v := by
  obtain ⟨b0, h0⟩ := Option.isSome_iff_exists.mp (present 0 (by decide))
  obtain ⟨b1, h1⟩ := Option.isSome_iff_exists.mp (present 1 (by decide))
  obtain ⟨b2, h2⟩ := Option.isSome_iff_exists.mp (present 2 (by decide))
  obtain ⟨b3, h3⟩ := Option.isSome_iff_exists.mp (present 3 (by decide))
  obtain ⟨b4, h4⟩ := Option.isSome_iff_exists.mp (present 4 (by decide))
  obtain ⟨b5, h5⟩ := Option.isSome_iff_exists.mp (present 5 (by decide))
  obtain ⟨b6, h6⟩ := Option.isSome_iff_exists.mp (present 6 (by decide))
  obtain ⟨b7, h7⟩ := Option.isSome_iff_exists.mp (present 7 (by decide))
  simp only [ArmCertValue.Physical.regionWord, List.range, List.range.loop, List.map, List.foldr, bind, pure]
  rw [show 8 * w = 8 * w + 0 from rfl, h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [Option.bind_some]
  exact ⟨_,rfl⟩

theorem append_byte (lo hi : BitVec 64) (t : Nat) (ht : t < 16) :
    (hi.append lo).extractLsb' (8 * t) 8 =
      if t < 8 then byteOf lo t else byteOf hi (t - 8) := by
  split
  · rename_i low
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [byteOf_getLsbD _ _ _ hk,BitVec.getLsbD_extractLsb']
    simp only [BitVec.append,BitVec.getLsbD_or,BitVec.getLsbD_shiftLeftZeroExtend,BitVec.getLsbD_setWidth']
    simp only [hk,show 8 * t + k<64 by omega,decide_true,Bool.true_and,
      Bool.not_true,Bool.false_and,Bool.false_or]
  · rename_i high
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [byteOf_getLsbD _ _ _ hk,BitVec.getLsbD_extractLsb']
    simp only [BitVec.append,BitVec.getLsbD_or,BitVec.getLsbD_shiftLeftZeroExtend,BitVec.getLsbD_setWidth']
    simp only [hk,show ¬8 * t + k<64 by omega,decide_true,decide_false,Bool.true_and,
      Bool.not_false,Bool.or_false,BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ 8 * t + k),
      show 8 * t + k - 64 = 8 * (t - 8) + k by omega]

theorem pair_exists (view : BytePA) (x : St) (r : Region) (w : Nat)
    (present : ∀ i, i < 16 → (ArmCertValue.Physical.regionByte view x r (8 * w + i)).isSome = true) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x r (8 * w + i) = some (data.extractLsb' (8 * i) 8) := by
  obtain ⟨lo,hlo⟩ := word_exists view x r w (fun i hi => present i (by omega))
  obtain ⟨hi,hhi⟩ := word_exists view x r (w + 1) (by
    intro i bound
    have h := present (8 + i) (by omega)
    simpa only [show 8 * w + (8 + i) = 8 * (w + 1) + i by omega] using h)
  refine ⟨hi.append lo,?_⟩
  intro i bound
  rw [append_byte lo hi i bound]
  split
  · rename_i low
    exact (regionWord_bytes view x r w lo).mp hlo i low
  · rename_i high
    have h := (regionWord_bytes view x r (w + 1) hi).mp hhi (i - 8) (by omega)
    simpa only [byteOf, ArmCertValue.MemRegion.shl_int, show 8 * (w + 1) + (i - 8) = 8 * w + i by omega] using h

theorem pair_of_agrees (view : BytePA) (vals : List (BitVec 64)) (σ : Sym) (x : St)
    (agrees : ArmCertValue.Physical.Agrees view vals σ x) (r : Region) (w : Nat)
    (tracked : ∀ i, i < 16 → (σ.memB r (8 * w + i)).isSome = true) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x r (8 * w + i) = some (data.extractLsb' (8 * i) 8) := by
  apply pair_exists
  intro i bound
  obtain ⟨⟨id,byte⟩,h⟩ := Option.isSome_iff_exists.mp (tracked i bound)
  rw [agrees.2.2 r (8 * w + i) id byte h]
  rfl

theorem pair_of_prefix (view : BytePA) (regions : List Region) (σ0 : Sym)
    (inputs : List (BitVec 64)) (plan : List ArmCertValue.F.Step) (k : Nat) (x : St)
    (r : Region) (w : Nat)
    (agreement : ArmCertPipe.F.AgreesAt view regions σ0 inputs plan k x)
    (checked : (ArmCertValue.F.compileRun regions σ0 inputs.length (plan.take k)).map
      (fun p => (List.range 16).all (fun i => (p.2.memB r (8 * w + i)).isSome)) = some true) :
    ∃ data : BitVec 128, ∀ i, i < 16 →
      ArmCertValue.Physical.regionByte view x r (8 * w + i) = some (data.extractLsb' (8 * i) 8) := by
  obtain ⟨ds,σ,hc,agrees,bounded⟩ := agreement
  rw [hc] at checked
  simp only [Option.map_some,Option.some.injEq] at checked
  apply pair_of_agrees view (extend inputs ds) σ x agrees r w
  intro i hi
  exact List.all_eq_true.mp checked i (List.mem_range.mpr hi)

#print axioms pair_of_prefix
#print axioms word_exists
#print axioms append_byte
#print axioms pair_exists
#print axioms pair_of_agrees
end ArmCertValue.PhysicalPairData
