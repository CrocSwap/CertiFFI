import ArmCertPipe.ValuePlan
import ArmCertValue.PhysicalMemory

open ArmCertValue
open HeapV2StepCerts.RegBind (Reg St)
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

namespace TranslateSpan.LegacyScalarEffects

theorem orr_zero_vholds (destination : Reg) (a b : Src) (source fin : St)
    (holds : VHolds [(destination,some ⟨.orr,[a,b]⟩)] none source fin) :
    VHolds [(destination,some ⟨.orrShl 0,[a,b]⟩)] none source fin := by
  refine ⟨?_,holds.2⟩
  intro reg
  have result := holds.1 reg
  by_cases equal : destination = reg
  · simp only [List.find?_cons, equal, decide_true, Option.map_some] at result ⊢
    change _ = srcVal source a ||| srcVal source b at result
    change _ = srcVal source a ||| (srcVal source b <<< (0 : Nat))
    rw [BitVec.shiftLeft_zero]
    exact result
  · simpa only [List.find?_cons, List.find?_nil, equal, decide_false,
      Bool.cond_false, Option.map_none] using result

theorem orr_zero_effect (language : ArmCertPipe.ValuePlan.Language)
    (view : Physical.BytePA) (regions : List Region) (destination : Reg) (a b : Src)
    (source fin : St) (holds : VHolds [(destination,some ⟨.orr,[a,b]⟩)] none source fin)
    (memory : fin.mem = source.mem) :
    ArmCertPipe.ValuePlan.Holds language view regions
      (ArmCertPipe.ValuePlan.legacy language ⟨[(destination,some ⟨.orrShl 0,[a,b]⟩)],none,[]⟩)
      source fin :=
  (ArmCertPipe.ValuePlan.holds_legacy language view regions _ source fin).mpr
    ⟨orr_zero_vholds destination a b source fin holds,
      Physical.memV_nil_of_mem view regions source fin memory⟩

#print axioms orr_zero_vholds
#print axioms orr_zero_effect

end TranslateSpan.LegacyScalarEffects
