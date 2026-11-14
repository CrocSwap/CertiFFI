import Pilot.S2Decode
import Pilot.S2Granule
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace S2DecodeAny
abbrev State := SequentialState Regs oracleChoiceSource
abbrev Result := EStateM.Result (Sail.Error exception) State TGx
noncomputable def native0 := S2Decode.native
theorem eq0 (s : State) : AArch64_S2DecodeTG0 0#2 s = native0 s := S2Decode.complete s
drive_spec native1, eq1 : fun (s : State) => AArch64_S2DecodeTG0 1#2 s
drive_spec native2, eq2 : fun (s : State) => AArch64_S2DecodeTG0 2#2 s
drive_spec reserved0, reserved_eq0 : fun (s : State)
    (hImpl : s.regs.bank_BitVec_2 .__impdef_TG0 = 0#2) =>
  AArch64_S2DecodeTG0 3#2 s
drive_spec reserved1, reserved_eq1 : fun (s : State)
    (hImpl : s.regs.bank_BitVec_2 .__impdef_TG0 = 1#2) =>
  AArch64_S2DecodeTG0 3#2 s
drive_spec reserved2, reserved_eq2 : fun (s : State)
    (hImpl : s.regs.bank_BitVec_2 .__impdef_TG0 = 2#2) =>
  AArch64_S2DecodeTG0 3#2 s
drive_spec reserved3, reserved_eq3 : fun (s : State)
    (hImpl : s.regs.bank_BitVec_2 .__impdef_TG0 = 3#2) =>
  AArch64_S2DecodeTG0 3#2 s
def value : Result → TGx
  | .ok x _ => x
  | .error _ _ => .TGx_4KB
def occ : Result → Std.ExtHashMap Nat Nat
  | .ok _ s => s.choiceOcc
  | .error _ s => s.choiceOcc
@[simp] theorem occ_native1 (s : State) : occ (native1 s) = occ (native0 s) := by rfl
@[simp] theorem occ_native2 (s : State) : occ (native2 s) = occ (native0 s) := by rfl
@[simp] theorem occ_reserved0 (s : State) : occ (reserved0 s) = occ (native0 s) := by rfl
@[simp] theorem occ_reserved1 (s : State) : occ (reserved1 s) = occ (native0 s) := by rfl
@[simp] theorem occ_reserved2 (s : State) : occ (reserved2 s) = occ (native0 s) := by rfl
@[simp] theorem occ_reserved3 (s : State) : occ (reserved3 s) = occ (native0 s) := by rfl
def choose {α : Type} (x : BitVec 2) (a b c d : α) : α :=
  if x = 0#2 then a else if x = 1#2 then b else if x = 2#2 then c else d
def impl (s : State) : BitVec 2 := s.regs.bank_BitVec_2 .__impdef_TG0
noncomputable def native3 (s : State) : Result :=
  .ok (choose (impl s) (value (reserved0 s)) (value (reserved1 s))
        (value (reserved2 s)) (value (reserved3 s)))
    {s with choiceOcc := occ (native0 s)}

theorem packed_reserved0 (s : State) :
    reserved0 s = .ok (value (reserved0 s)) {s with choiceOcc := occ (reserved0 s)} := by
  delta reserved0
  rfl
theorem packed_reserved1 (s : State) :
    reserved1 s = .ok (value (reserved1 s)) {s with choiceOcc := occ (reserved1 s)} := by
  delta reserved1
  rfl
theorem packed_reserved2 (s : State) :
    reserved2 s = .ok (value (reserved2 s)) {s with choiceOcc := occ (reserved2 s)} := by
  delta reserved2
  rfl
theorem packed_reserved3 (s : State) :
    reserved3 s = .ok (value (reserved3 s)) {s with choiceOcc := occ (reserved3 s)} := by
  delta reserved3
  rfl
theorem complete3 (s : State) : AArch64_S2DecodeTG0 3#2 s = native3 s := by
  by_cases h0 : impl s = 0#2
  · simpa only [native3, occ_reserved0, occ_reserved1, occ_reserved2, occ_reserved3, choose, ite_eq_left h0] using (reserved_eq0 s h0).trans (packed_reserved0 s)
  by_cases h1 : impl s = 1#2
  · simpa only [native3, occ_reserved0, occ_reserved1, occ_reserved2, occ_reserved3, choose, ite_eq_right h0, ite_eq_left h1] using (reserved_eq1 s h1).trans (packed_reserved1 s)
  by_cases h2 : impl s = 2#2
  · simpa only [native3, occ_reserved0, occ_reserved1, occ_reserved2, occ_reserved3, choose, ite_eq_right h0, ite_eq_right h1, ite_eq_left h2] using (reserved_eq2 s h2).trans (packed_reserved2 s)
  have h3 : impl s = 3#2 := by
    have hb := (impl s).isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *
    omega
  simpa only [native3, occ_reserved0, occ_reserved1, occ_reserved2, occ_reserved3, choose, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2] using
    (reserved_eq3 s h3).trans (packed_reserved3 s)
noncomputable def native (tg0 : BitVec 2) (s : State) : Result :=
  .ok (choose tg0 (value (native0 s)) (value (native1 s)) (value (native2 s)) (value (native3 s)))
    {s with choiceOcc := occ (native0 s)}

theorem packed0 (s : State) :
    native0 s = .ok (value (native0 s)) {s with choiceOcc := occ (native0 s)} := by
  delta native0
  delta S2Decode.native
  rfl
theorem packed1 (s : State) :
    native1 s = .ok (value (native1 s)) {s with choiceOcc := occ (native1 s)} := by
  delta native1
  rfl
theorem packed2 (s : State) :
    native2 s = .ok (value (native2 s)) {s with choiceOcc := occ (native2 s)} := by
  delta native2
  rfl
theorem packed3 (s : State) :
    native3 s = .ok (value (native3 s)) {s with choiceOcc := occ (native3 s)} := by
  delta native3
  rfl
@[simp] theorem occ_native3 (s : State) : occ (native3 s) = occ (native0 s) := by rfl
theorem complete (tg0 : BitVec 2) (s : State) : AArch64_S2DecodeTG0 tg0 s = native tg0 s := by
  by_cases h0 : tg0 = 0#2
  · simpa [native, choose, occ_native1, occ_native2, occ_native3, h0] using (eq0 s).trans (packed0 s)
  by_cases h1 : tg0 = 1#2
  · simpa [native, choose, occ_native1, occ_native2, occ_native3, h1] using (eq1 s).trans (packed1 s)
  by_cases h2 : tg0 = 2#2
  · simpa [native, choose, occ_native1, occ_native2, occ_native3, h2] using (eq2 s).trans (packed2 s)
  have h3 : tg0 = 3#2 := by
    have hb := tg0.isLt
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *
    omega
  simpa [native, choose, occ_native1, occ_native2, occ_native3, h3] using (complete3 s).trans (packed3 s)
attribute [step_summary] complete
#print axioms complete
end S2DecodeAny
