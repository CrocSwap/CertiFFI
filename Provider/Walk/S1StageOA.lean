import Walk.S1EL10PermsCallees
import Pilot.S1DecodeFacts
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
namespace S1StageOA
abbrev State := S1Normality.State

def span (w : TTWState) : Nat :=
  (if w.level = 1 then 30 else if w.level = 2 then 21 else 12) +
    (if w.contiguous = 1#1 then 4 else 0)

def address (ia : BitVec 64) (w : TTWState) : FullAddress :=
  {paspace := w.baseaddress.paspace
   address := Sail.BitVec.castWidth (m := 56)
     ((Sail.BitVec.extractLsb w.baseaddress.address 55 (span w)) +++
       (Sail.BitVec.extractLsb ia (span w - 1) 0))}

theorem total (ia : BitVec 64) (w : TTWState) (s : State)
    (hLevel : 1 ≤ w.level ∧ w.level ≤ 3) :
    ∃ t : State, StageOA ia 0#1 .TGx_4KB w s = .ok (address ia w) t ∧
      S1Normality.Frame s t := by
  let k1 := s.choiceOcc.getD 1246 0
  let u1 : State := {s with choiceOcc := s.choiceOcc.insert 1246 (k1 + 1)}
  have hl1 : occLabel 1246 s = .ok (.occ 1246 k1) u1 := rfl
  rcases S1Unknowns.undefined_full_address_total (.occ 1246 k1) u1 with
    ⟨unused, t1, hu, hr1, hm1, he1⟩
  let k2 := t1.choiceOcc.getD 1247 0
  let u2 : State := {t1 with choiceOcc := t1.choiceOcc.insert 1247 (k2 + 1)}
  have hl2 : occLabel 1247 t1 = .ok (.occ 1247 k2) u2 := rfl
  rcases S1EL10PermsCallees.int_normal (.occ 1247 k2) u2 with
    ⟨unusedInt, t, hi, hr2, hm2, he2⟩
  refine ⟨t, ?_, hr2.trans hr1, hm2.trans hm1, he2.trans he1⟩
  rcases w with ⟨isTable, level, base, contig, assured, s2only, disch, ng, guarded, sdf, domain, attrs, perms⟩
  change 1 ≤ level ∧ level ≤ 3 at hLevel
  have hCases : level = 1 ∨ level = 2 ∨ level = 3 := by omega
  have hContig := S1DecodeFacts.bit_cases contig
  rcases hCases with rfl | rfl | rfl <;> rcases hContig with rfl | rfl
  all_goals
    simp [StageOA, TranslationSize, TGxGranuleBits, FINAL_LEVEL, ContiguousSize,
      address, span, ArmFull.assert, PreSail.assert, Bind.bind, Pure.pure,
      EStateM.bind, EStateM.pure, Functor.map, EStateM.map, hl1, hu, hl2, hi]
  all_goals rfl
#print axioms total
end S1StageOA
