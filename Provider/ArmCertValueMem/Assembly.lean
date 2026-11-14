-- Memory: generic MemVHolds assembly facts for the heap-v2 memory steps.
import HeapV2StepCerts.AccShape
import HeapV2StepCerts.ActionTransport
import HeapV2StepCerts.BodyHolds
import HeapV2StepCerts.BodyMemD
import HeapV2StepCerts.C3Byte
import HeapV2StepCerts.C3Core
import HeapV2StepCerts.C3Pair
import HeapV2StepCerts.Carry
import HeapV2StepCerts.CodeScope
import HeapV2StepCerts.DataBytes
import HeapV2StepCerts.FetchFrames
import HeapV2StepCerts.MemConfigFrame
import HeapV2StepCerts.MemHolds
import HeapV2StepCerts.MemNextV3
import HeapV2StepCerts.MemRunD
import HeapV2StepCerts.MemStepV3
import HeapV2StepCerts.MemSteps
import HeapV2StepCerts.MemStepsV3
import HeapV2StepCerts.MemStepsV3_00
import HeapV2StepCerts.MemStepsV3_01
import HeapV2StepCerts.MemStepsV3_02
import HeapV2StepCerts.MemStepsV3_03
import HeapV2StepCerts.MemStepsV3_04
import HeapV2StepCerts.MemStepsV3_05
import HeapV2StepCerts.MemTailD
import HeapV2StepCerts.MemTailLdrb
import HeapV2StepCerts.MemTailPair
import HeapV2StepCerts.MemTailStrb
import HeapV2StepCerts.RawFetch
import HeapV2StepCerts.RegBind
import HeapV2StepCerts.RegBindCore
import HeapV2StepCerts.RegBindData
import HeapV2StepCerts.RegVal
import HeapV2StepCerts.Straight
import HeapV2StepCerts.StraightV2
import HeapV2StepCerts.ValueTailDef
import ArmCertValueMem.Premises
import ArmCertValueMem.Region
import HeapV2StepCerts.ValuePay
import RtS3.MemFacts2
set_option autoImplicit false
namespace ArmCertValue.HeapV2Mem
open ArmCertValue ArmCertValue.MemRegion ArmCert.Translate.Model
open HeapV2StepCerts.RegBind (St regVal)

/-- **Byte frame from a write cover**: if every written PA is the PA of one of the step's own stored region bytes,
every OTHER tracked byte reads the same before and after (RegionsInjective). -/
theorem frame_of_cover (mapping : BitVec 64 → Option Nat) (p : HeapV2E17.Pins) (x y : St) (written : Nat → Prop)
    (wo : ArmCert.Translate.WritesOnly written (fun a => x.mem[a]?) (fun a => y.mem[a]?))
    (stored : List (Region × Nat))
    (cover : ∀ m, written m → ∃ b, b ∈ stored ∧ mapping (byteVA p b.1 b.2) = some m)
    (inj : RegionsInjective p mapping) (hst : ∀ b, b ∈ stored → b ∈ heapv2Bytes)
    (r : Region) (j : Nat) (hrj : (r, j) ∈ heapv2Bytes) (hns : (r, j) ∉ stored) :
    regionByte mapping (pinv p) y r j = regionByte mapping (pinv p) x r j := by
  rw [regionByte_va, regionByte_va]
  cases h : mapping (byteVA p r j) with
  | none => rfl
  | some m =>
    simp only [Option.bind_some]
    apply wo m
    intro hw
    obtain ⟨b, hb, hbm⟩ := cover m hw
    exact inj (r, j) hrj b (hst b hb) (fun e => hns (e ▸ hb)) m h hbm

/-- Tracked bytes: membership of (r, j) for r a region and j < 8 * r.words. -/
theorem mem_heapv2Bytes {r : Region} {j : Nat} (hr : r ∈ regions) (hj : j < 8 * r.words) : (r, j) ∈ heapv2Bytes := by
  unfold heapv2Bytes
  exact List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩

/-- DataBytesLinear at one access byte. -/
theorem dbl_at {p : HeapV2E17.Pins} {mapping : BitVec 64 → Option Nat} (h : DataBytesLinear p mapping)
    {e : Nat × Nat × Int × Nat × Bool} (he : e ∈ HeapV2Plan.symbolicAccesses) {i : Nat} (hi : i < e.2.2.2.1) :
    mapping (BitVec.ofInt 64 ((HeapV2E17.pin p e.2.1 : Int) + e.2.2.1 + i)) = (mapping (HeapV2E17.dataVA p e)).map (· + i) := by
  have a := List.all_eq_true.1 h e he
  have b := List.all_eq_true.1 a i (List.mem_range.2 hi)
  simpa using b

/-- LDRB's value is the zero-extended byte. -/
theorem ldrbVal_eq (b : BitVec 8) : ArmCertMem.LdrbEval.ldrbVal b = b.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [ArmCertMem.LdrbEval.ldrbVal, Sail.BitVec.zeroExtend, Sail.BitVec.castWidth, BitVec.getLsbD_setWidth]
  all_goals omega

/-- The bytes of LDP's halves. -/
theorem byteOf_ldpLo (d : BitVec 128) (k : Nat) (hk : k < 8) :
    byteOf (ArmCertMem.LdpEval.ldpLo d) k = d.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [byteOf_getLsbD _ _ _ hi]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ArmCertMem.LdpEval.ldpLo, Sail.BitVec.zeroExtend, Sail.BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb']

theorem byteOf_ldpHi (d : BitVec 128) (k : Nat) (hk : k < 8) :
    byteOf (ArmCertMem.LdpEval.ldpHi d) k = d.extractLsb' (8 * (k + 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [byteOf_getLsbD _ _ _ hi]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ArmCertMem.LdpEval.ldpHi, Sail.BitVec.zeroExtend, Sail.BitVec.castWidth, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb']

/-- The slot bytes of an STP (Rt low, Rt2 high). -/
theorem slotByte_lo (a b : BitVec 64) (k : Nat) (hk : k < 8) : RtSaved.slotByte a b k = byteOf a k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [byteOf_getLsbD _ _ _ hi]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [RtSaved.slotByte, BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_append, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false, decide_true,
      decide_false, Bool.true_and, Bool.false_and, Bool.and_true] <;> simp

theorem slotByte_hi (a b : BitVec 64) (k : Nat) (hk : k < 8) : RtSaved.slotByte a b (8 + k) = byteOf b k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [byteOf_getLsbD _ _ _ hi]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [RtSaved.slotByte, BitVec.append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_append, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false, decide_true,
      decide_false, Bool.true_and, Bool.false_and, Bool.and_true] <;> simp

#print axioms frame_of_cover
#print axioms ldrbVal_eq
#print axioms byteOf_ldpLo
#print axioms byteOf_ldpHi
#print axioms slotByte_lo
#print axioms slotByte_hi
end ArmCertValue.HeapV2Mem
