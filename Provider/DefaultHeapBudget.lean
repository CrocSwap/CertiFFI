import Lean
namespace ReleaseProfile.DefaultHeapBudget
set_option autoImplicit false
set_option maxHeartbeats 100000

def costAt : Nat → Nat
  | 11 => 1
  | 18 => 1
  | 19 => 1
  | 22 => 1
  | 23 => 1
  | 26 => 1
  | 27 => 1
  | 30 => 1
  | 31 => 1
  | 34 => 1
  | 35 => 1
  | 38 => 1
  | 39 => 1
  | 42 => 1
  | 43 => 1
  | 46 => 1
  | 47 => 1
  | 50 => 1
  | 51 => 1
  | 54 => 1
  | 55 => 1
  | 58 => 1
  | 59 => 1
  | 62 => 1
  | 63 => 1
  | 66 => 1
  | 67 => 1
  | 70 => 1
  | 71 => 1
  | 74 => 1
  | 75 => 1
  | 78 => 1
  | 79 => 1
  | 82 => 1
  | 83 => 1
  | 86 => 1
  | 87 => 1
  | 90 => 1
  | 91 => 1
  | 94 => 1
  | 95 => 1
  | 98 => 1
  | 99 => 1
  | 102 => 1
  | 103 => 1
  | 106 => 1
  | 107 => 1
  | 110 => 1
  | 111 => 1
  | 114 => 1
  | 115 => 1
  | 118 => 1
  | 119 => 1
  | 122 => 1
  | 123 => 1
  | 126 => 1
  | 127 => 1
  | 130 => 1
  | 131 => 1
  | 134 => 1
  | 135 => 1
  | 138 => 1
  | 139 => 1
  | 142 => 1
  | 143 => 1
  | 153 => 1
  | 156 => 1
  | 159 => 1
  | 162 => 1
  | 165 => 1
  | 168 => 1
  | 171 => 1
  | 174 => 1
  | 177 => 1
  | 180 => 1
  | 183 => 1
  | 186 => 1
  | 189 => 1
  | 192 => 1
  | 195 => 1
  | 198 => 1
  | 201 => 1
  | 204 => 1
  | 207 => 1
  | 210 => 1
  | 213 => 1
  | 216 => 1
  | 219 => 1
  | 222 => 1
  | 225 => 1
  | 228 => 1
  | 231 => 1
  | 234 => 1
  | 237 => 1
  | 240 => 1
  | 243 => 1
  | 246 => 1
  | 253 => 2
  | 256 => 2
  | 329 => 2
  | 330 => 2
  | 351 => 1
  | 352 => 1
  | 353 => 1
  | 354 => 1
  | 355 => 1
  | _ => 0

theorem cost_at_11 : costAt 11 = 1 := rfl

theorem cost_at_18 : costAt 18 = 1 := rfl

theorem cost_at_19 : costAt 19 = 1 := rfl

theorem cost_at_22 : costAt 22 = 1 := rfl

theorem cost_at_23 : costAt 23 = 1 := rfl

theorem cost_at_26 : costAt 26 = 1 := rfl

theorem cost_at_27 : costAt 27 = 1 := rfl

theorem cost_at_30 : costAt 30 = 1 := rfl

theorem cost_at_31 : costAt 31 = 1 := rfl

theorem cost_at_34 : costAt 34 = 1 := rfl

theorem cost_at_35 : costAt 35 = 1 := rfl

theorem cost_at_38 : costAt 38 = 1 := rfl

theorem cost_at_39 : costAt 39 = 1 := rfl

theorem cost_at_42 : costAt 42 = 1 := rfl

theorem cost_at_43 : costAt 43 = 1 := rfl

theorem cost_at_46 : costAt 46 = 1 := rfl

theorem cost_at_47 : costAt 47 = 1 := rfl

theorem cost_at_50 : costAt 50 = 1 := rfl

theorem cost_at_51 : costAt 51 = 1 := rfl

theorem cost_at_54 : costAt 54 = 1 := rfl

theorem cost_at_55 : costAt 55 = 1 := rfl

theorem cost_at_58 : costAt 58 = 1 := rfl

theorem cost_at_59 : costAt 59 = 1 := rfl

theorem cost_at_62 : costAt 62 = 1 := rfl

theorem cost_at_63 : costAt 63 = 1 := rfl

theorem cost_at_66 : costAt 66 = 1 := rfl

theorem cost_at_67 : costAt 67 = 1 := rfl

theorem cost_at_70 : costAt 70 = 1 := rfl

theorem cost_at_71 : costAt 71 = 1 := rfl

theorem cost_at_74 : costAt 74 = 1 := rfl

theorem cost_at_75 : costAt 75 = 1 := rfl

theorem cost_at_78 : costAt 78 = 1 := rfl

theorem cost_at_79 : costAt 79 = 1 := rfl

theorem cost_at_82 : costAt 82 = 1 := rfl

theorem cost_at_83 : costAt 83 = 1 := rfl

theorem cost_at_86 : costAt 86 = 1 := rfl

theorem cost_at_87 : costAt 87 = 1 := rfl

theorem cost_at_90 : costAt 90 = 1 := rfl

theorem cost_at_91 : costAt 91 = 1 := rfl

theorem cost_at_94 : costAt 94 = 1 := rfl

theorem cost_at_95 : costAt 95 = 1 := rfl

theorem cost_at_98 : costAt 98 = 1 := rfl

theorem cost_at_99 : costAt 99 = 1 := rfl

theorem cost_at_102 : costAt 102 = 1 := rfl

theorem cost_at_103 : costAt 103 = 1 := rfl

theorem cost_at_106 : costAt 106 = 1 := rfl

theorem cost_at_107 : costAt 107 = 1 := rfl

theorem cost_at_110 : costAt 110 = 1 := rfl

theorem cost_at_111 : costAt 111 = 1 := rfl

theorem cost_at_114 : costAt 114 = 1 := rfl

theorem cost_at_115 : costAt 115 = 1 := rfl

theorem cost_at_118 : costAt 118 = 1 := rfl

theorem cost_at_119 : costAt 119 = 1 := rfl

theorem cost_at_122 : costAt 122 = 1 := rfl

theorem cost_at_123 : costAt 123 = 1 := rfl

theorem cost_at_126 : costAt 126 = 1 := rfl

theorem cost_at_127 : costAt 127 = 1 := rfl

theorem cost_at_130 : costAt 130 = 1 := rfl

theorem cost_at_131 : costAt 131 = 1 := rfl

theorem cost_at_134 : costAt 134 = 1 := rfl

theorem cost_at_135 : costAt 135 = 1 := rfl

theorem cost_at_138 : costAt 138 = 1 := rfl

theorem cost_at_139 : costAt 139 = 1 := rfl

theorem cost_at_142 : costAt 142 = 1 := rfl

theorem cost_at_143 : costAt 143 = 1 := rfl

theorem cost_at_153 : costAt 153 = 1 := rfl

theorem cost_at_156 : costAt 156 = 1 := rfl

theorem cost_at_159 : costAt 159 = 1 := rfl

theorem cost_at_162 : costAt 162 = 1 := rfl

theorem cost_at_165 : costAt 165 = 1 := rfl

theorem cost_at_168 : costAt 168 = 1 := rfl

theorem cost_at_171 : costAt 171 = 1 := rfl

theorem cost_at_174 : costAt 174 = 1 := rfl

theorem cost_at_177 : costAt 177 = 1 := rfl

theorem cost_at_180 : costAt 180 = 1 := rfl

theorem cost_at_183 : costAt 183 = 1 := rfl

theorem cost_at_186 : costAt 186 = 1 := rfl

theorem cost_at_189 : costAt 189 = 1 := rfl

theorem cost_at_192 : costAt 192 = 1 := rfl

theorem cost_at_195 : costAt 195 = 1 := rfl

theorem cost_at_198 : costAt 198 = 1 := rfl

theorem cost_at_201 : costAt 201 = 1 := rfl

theorem cost_at_204 : costAt 204 = 1 := rfl

theorem cost_at_207 : costAt 207 = 1 := rfl

theorem cost_at_210 : costAt 210 = 1 := rfl

theorem cost_at_213 : costAt 213 = 1 := rfl

theorem cost_at_216 : costAt 216 = 1 := rfl

theorem cost_at_219 : costAt 219 = 1 := rfl

theorem cost_at_222 : costAt 222 = 1 := rfl

theorem cost_at_225 : costAt 225 = 1 := rfl

theorem cost_at_228 : costAt 228 = 1 := rfl

theorem cost_at_231 : costAt 231 = 1 := rfl

theorem cost_at_234 : costAt 234 = 1 := rfl

theorem cost_at_237 : costAt 237 = 1 := rfl

theorem cost_at_240 : costAt 240 = 1 := rfl

theorem cost_at_243 : costAt 243 = 1 := rfl

theorem cost_at_246 : costAt 246 = 1 := rfl

theorem cost_at_253 : costAt 253 = 2 := rfl

theorem cost_at_256 : costAt 256 = 2 := rfl

theorem cost_at_329 : costAt 329 = 2 := rfl

theorem cost_at_330 : costAt 330 = 2 := rfl

theorem cost_at_351 : costAt 351 = 1 := rfl

theorem cost_at_352 : costAt 352 = 1 := rfl

theorem cost_at_353 : costAt 353 = 1 := rfl

theorem cost_at_354 : costAt 354 = 1 := rfl

theorem cost_at_355 : costAt 355 = 1 := rfl

def prefixDraws : Nat → Nat
  | 0 => 0
  | k + 1 => prefixDraws k + costAt k

def capacity : Nat := prefixDraws 357

set_option maxRecDepth 2048 in
theorem capacity_eq : capacity = 110 := rfl

theorem prefix_mono (k n : Nat) (bound : k ≤ n) : prefixDraws k ≤ prefixDraws n := by
  induction bound with
  | refl => exact Nat.le_refl _
  | @step n priorBound prefixBound =>
    exact Nat.le_trans prefixBound (Nat.le_add_right _ _)

theorem rows_room (k : Nat) (bound : k < 357) : prefixDraws k + costAt k ≤ capacity := by
  exact prefix_mono (k + 1) 357 bound

theorem rows_next (k : Nat) : prefixDraws k + costAt k ≤ prefixDraws (k + 1) := Nat.le_refl _

#print axioms capacity_eq
#print axioms prefix_mono
#print axioms rows_room
#print axioms rows_next
end ReleaseProfile.DefaultHeapBudget
