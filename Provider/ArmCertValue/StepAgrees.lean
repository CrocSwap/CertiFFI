-- ArmCert VALUE LAYER: the one generic step theorem. Given the actual step's value facts
-- (per-class `VHolds`, memory `MemVHolds`) and a successful `compile`, `Agrees` is carried across the step
-- on the extended table.
import ArmCertValue.Compile
import ArmCertValue.Bytes
open Sail Sail.ConcurrencyInterfaceV1 ArmFull
set_option autoImplicit false
namespace ArmCertValue
open HeapV2StepCerts.RegBind (Reg St regVal)

theorem getD_left (vals L : List (BitVec 64)) (i : Nat) (h : i < vals.length) :
    (vals ++ L).getD i 0 = vals.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_right (vals L : List (BitVec 64)) (j : Nat) :
    (vals ++ L).getD (vals.length + j) 0 = L.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

theorem getD_map_of (vals : List (BitVec 64)) (D : List Def) (j : Nat) (d : Def) (h : D[j]? = some d) :
    (D.map (Def.eval vals)).getD j 0 = d.eval vals := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, h, Option.map_some, Option.getD_some]

theorem lt_of_getElem?_some {α : Type} (D : List α) (j : Nat) (d : α) (h : D[j]? = some d) : j < D.length := by
  rcases Nat.lt_or_ge j D.length with hj | hj
  · exact hj
  · rw [List.getElem?_eq_none hj] at h; cases h

theorem zext_byte (v : BitVec 64) : (v.setWidth 8).setWidth 64 = v &&& 0xff#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_and,
    show (0xff#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem getD_defs_left (vals : List (BitVec 64)) (rds fds : List Def) (j : Nat) (d : Def)
    (h : rds[j]? = some d) : ((rds ++ fds).map (Def.eval vals)).getD j 0 = d.eval vals := by
  have hj : j < rds.length := by
    rcases Nat.lt_or_ge j rds.length with hj | hj
    · exact hj
    · rw [List.getElem?_eq_none hj] at h; cases h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_append_left hj, h,
    Option.map_some, Option.getD_some]

theorem getD_defs_right (vals : List (BitVec 64)) (rds fds : List Def) (t : Nat) (d : Def)
    (h : fds[t]? = some d) : ((rds ++ fds).map (Def.eval vals)).getD (rds.length + t) 0 = d.eval vals := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, h,
    Option.map_some, Option.getD_some]

theorem flagDefs_spec {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {vals : List (BitVec 64)}
    {σ : Sym} {x : St} (hA : Agrees mapping pinv vals σ x) (hB : σ.Bounded vals.length)
    (a b c d : VUpd) (fds : List Def) (h : flagDefs σ (some (a, b, c, d)) = some fds) :
    ∃ a' b' c' d', fds = [a', b', c', d'] ∧
      a'.eval vals = a.eval x ∧ b'.eval vals = b.eval x ∧ c'.eval vals = c.eval x ∧ d'.eval vals = d.eval x ∧
      a'.Below vals.length ∧ b'.Below vals.length ∧ c'.Below vals.length ∧ d'.Below vals.length := by
  simp only [flagDefs] at h
  split at h
  · next a' b' c' d' ha hb hc hd =>
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨ea, ba⟩ := defOf_sound hA hB a a' ha
    obtain ⟨eb, bb⟩ := defOf_sound hA hB b b' hb
    obtain ⟨ec, bc⟩ := defOf_sound hA hB c c' hc
    obtain ⟨ed, bd⟩ := defOf_sound hA hB d d' hd
    exact ⟨a', b', c', d', rfl, ea, eb, ec, ed, ba, bb, bc, bd⟩
  · simp at h

theorem bytesOf_spec {σ : Sym} {g : Region} {w : Nat} {as : List Arg} {ks : List Nat}
    (h : bytesOf σ g w = some (as, ks)) :
    ∃ i0 i1 i2 i3 i4 i5 i6 i7 k0 k1 k2 k3 k4 k5 k6 k7,
      as = [.id i0, .id i1, .id i2, .id i3, .id i4, .id i5, .id i6, .id i7] ∧ ks = [k0, k1, k2, k3, k4, k5, k6, k7] ∧
      σ.memB g (8 * w + 0) = some (i0, k0) ∧ σ.memB g (8 * w + 1) = some (i1, k1) ∧
      σ.memB g (8 * w + 2) = some (i2, k2) ∧ σ.memB g (8 * w + 3) = some (i3, k3) ∧
      σ.memB g (8 * w + 4) = some (i4, k4) ∧ σ.memB g (8 * w + 5) = some (i5, k5) ∧
      σ.memB g (8 * w + 6) = some (i6, k6) ∧ σ.memB g (8 * w + 7) = some (i7, k7) := by
  unfold bytesOf at h
  split at h
  · next i0 k0 i1 k1 i2 k2 i3 k3 i4 k4 i5 k5 i6 k6 i7 k7 e0 e1 e2 e3 e4 e5 e6 e7 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨i0, i1, i2, i3, i4, i5, i6, i7, k0, k1, k2, k3, k4, k5, k6, k7, rfl, rfl,
      by simpa using e0, e1, e2, e3, e4, e5, e6, e7⟩
  · simp at h

theorem bytes4Of_spec {σ : Sym} {g : Region} {j : Nat} {as : List Arg} {ks : List Nat}
    (h : bytes4Of σ g j = some (as, ks)) :
    ∃ i0 i1 i2 i3 k0 k1 k2 k3, as = [.id i0, .id i1, .id i2, .id i3] ∧ ks = [k0, k1, k2, k3] ∧
      σ.memB g (j + 0) = some (i0, k0) ∧ σ.memB g (j + 1) = some (i1, k1) ∧
      σ.memB g (j + 2) = some (i2, k2) ∧ σ.memB g (j + 3) = some (i3, k3) := by
  unfold bytes4Of at h
  split at h
  · next i0 k0 i1 k1 i2 k2 i3 k3 e0 e1 e2 e3 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨i0, i1, i2, i3, k0, k1, k2, k3, rfl, rfl, e0, e1, e2, e3⟩
  · simp at h

/-- A load's definition evaluates to the loaded register's new value. -/
theorem loadDef_sound {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {vals : List (BitVec 64)}
    {σ : Sym} {x y : St} {regions : List Region} {effs : List MemEff}
    (hcoh : RegionCoherent mapping pinv) (hA : Agrees mapping pinv vals σ x)
    (hm : MemVHolds mapping pinv regions effs x y) (e : MemEff) (me : e ∈ effs) (r : Reg)
    (hr : loadReg e = some r) (d : Def) (hd : loadDef σ e = some d) : d.eval vals = regVal y r := by
  cases e with
  | load rt g w =>
    simp only [loadReg, Option.some.injEq] at hr
    subst hr
    simp only [loadDef, Option.map_eq_some_iff] at hd
    obtain ⟨⟨as, ks⟩, hb, rfl⟩ := hd
    obtain ⟨i0, i1, i2, i3, i4, i5, i6, i7, k0, k1, k2, k3, k4, k5, k6, k7, rfl, rfl,
      e0, e1, e2, e3, e4, e5, e6, e7⟩ := bytesOf_spec hb
    have hw := hm.1 _ me
    simp only at hw
    have c := hcoh x g w (regVal y rt) hw
    have byt : ∀ t i k, t < 8 → σ.memB g (8 * w + t) = some (i, k) →
        ((vals.getD i 0) >>> (8 * k)).setWidth 8 = ((regVal y rt) >>> (8 * t)).setWidth 8 := by
      intro t i k ht hmb
      have := c t ht
      rw [hA.2.2 g (8 * w + t) i k hmb, Option.some.injEq] at this
      exact this
    exact asm8_eval vals i0 i1 i2 i3 i4 i5 i6 i7 k0 k1 k2 k3 k4 k5 k6 k7 _
      (byt 0 i0 k0 (by omega) e0) (byt 1 i1 k1 (by omega) e1) (byt 2 i2 k2 (by omega) e2)
      (byt 3 i3 k3 (by omega) e3) (byt 4 i4 k4 (by omega) e4) (byt 5 i5 k5 (by omega) e5)
      (byt 6 i6 k6 (by omega) e6) (byt 7 i7 k7 (by omega) e7)
  | loadb rt g j =>
    simp only [loadReg, Option.some.injEq] at hr
    subst hr
    simp only [loadDef, Option.map_eq_some_iff] at hd
    obtain ⟨⟨i, k⟩, hmb, rfl⟩ := hd
    obtain ⟨b, hb, hyb⟩ := hm.1 _ me
    rw [hA.2.2 g j i k hmb, Option.some.injEq] at hb
    rw [hyb, ← hb, zext_byte']
    rfl
  | load32 rt g j =>
    simp only [loadReg, Option.some.injEq] at hr
    subst hr
    simp only [loadDef, Option.map_eq_some_iff] at hd
    obtain ⟨⟨as, ks⟩, hb, rfl⟩ := hd
    obtain ⟨i0, i1, i2, i3, k0, k1, k2, k3, rfl, rfl, e0, e1, e2, e3⟩ := bytes4Of_spec hb
    obtain ⟨u, hu, hbytes, hyu⟩ := hm.1 _ me
    have byt : ∀ t i k, t < 4 → σ.memB g (j + t) = some (i, k) →
        ((vals.getD i 0) >>> (8 * k)).setWidth 8 = (u >>> (8 * t)).setWidth 8 := by
      intro t i k ht hmb
      have := hbytes t ht
      rw [hA.2.2 g (j + t) i k hmb, Option.some.injEq] at this
      exact this
    rw [hyu]
    exact asm4_eval vals i0 i1 i2 i3 k0 k1 k2 k3 u hu (byt 0 i0 k0 (by omega) e0) (byt 1 i1 k1 (by omega) e1)
      (byt 2 i2 k2 (by omega) e2) (byt 3 i3 k3 (by omega) e3)
  | store _ _ _ => simp [loadReg] at hr
  | storeb _ _ _ => simp [loadReg] at hr
  | store32 _ _ _ => simp [loadReg] at hr

theorem loadDef_below {vals : List (BitVec 64)} {σ : Sym} (hB : σ.Bounded vals.length) (e : MemEff) (d : Def)
    (hd : loadDef σ e = some d) : d.Below vals.length := by
  cases e with
  | load rt g w =>
    simp only [loadDef, Option.map_eq_some_iff] at hd
    obtain ⟨⟨as, ks⟩, hb, rfl⟩ := hd
    obtain ⟨i0, i1, i2, i3, i4, i5, i6, i7, k0, k1, k2, k3, k4, k5, k6, k7, rfl, rfl,
      e0, e1, e2, e3, e4, e5, e6, e7⟩ := bytesOf_spec hb
    intro a ma
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ma
    rcases ma with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hB.2.2 _ _ _ _ e0
    · exact hB.2.2 _ _ _ _ e1
    · exact hB.2.2 _ _ _ _ e2
    · exact hB.2.2 _ _ _ _ e3
    · exact hB.2.2 _ _ _ _ e4
    · exact hB.2.2 _ _ _ _ e5
    · exact hB.2.2 _ _ _ _ e6
    · exact hB.2.2 _ _ _ _ e7
  | loadb rt g j =>
    simp only [loadDef, Option.map_eq_some_iff] at hd
    obtain ⟨⟨i, k⟩, hmb, rfl⟩ := hd
    intro a ma
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ma
    subst ma
    exact hB.2.2 _ _ _ _ hmb
  | load32 rt g j =>
    simp only [loadDef, Option.map_eq_some_iff] at hd
    obtain ⟨⟨as, ks⟩, hb, rfl⟩ := hd
    obtain ⟨i0, i1, i2, i3, k0, k1, k2, k3, rfl, rfl, e0, e1, e2, e3⟩ := bytes4Of_spec hb
    intro a ma
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ma
    rcases ma with rfl | rfl | rfl | rfl
    · exact hB.2.2 _ _ _ _ e0
    · exact hB.2.2 _ _ _ _ e1
    · exact hB.2.2 _ _ _ _ e2
    · exact hB.2.2 _ _ _ _ e3
  | store _ _ _ => simp [loadDef] at hd
  | storeb _ _ _ => simp [loadDef] at hd
  | store32 _ _ _ => simp [loadDef] at hd

set_option maxHeartbeats 400000 in
theorem step_agrees {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {vals : List (BitVec 64)}
    {σ σ' : Sym} {x y : St} {regions : List Region} {st : StepV} {ds : List Def}
    (hcoh : RegionCoherent mapping pinv)
    (hA : Agrees mapping pinv vals σ x) (hB : σ.Bounded vals.length)
    (hv : VHolds st.us st.fl x y) (hm : MemVHolds mapping pinv regions st.mem x y)
    (hc : compile σ vals.length regions st = some (ds, σ')) :
    Agrees mapping pinv (extend vals ds) σ' y ∧ σ'.Bounded (extend vals ds).length := by
  unfold compile at hc
  split at hc
  case h_2 => simp at hc
  next rds fds hr hf =>
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have rbelow := regDefs_below hA hB st.us rds hr
  have fbelow : ∀ d ∈ fds, d.Below vals.length := by
    cases hfl : st.fl with
    | none =>
      rw [hfl] at hf; simp only [flagDefs, Option.some.injEq] at hf; subst hf; simp
    | some q =>
      obtain ⟨a, b, c, d⟩ := q
      rw [hfl] at hf
      obtain ⟨a', b', c', d', rfl, -, -, -, -, ba, bb, bc, bd⟩ := flagDefs_spec hA hB a b c d fds hf
      intro e me
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at me
      rcases me with rfl | rfl | rfl | rfl <;> assumption
  have mbelow : ∀ d ∈ memDefs σ st.mem, d.Below vals.length := by
    intro d md
    obtain ⟨e, -, he⟩ := memDefs_mem σ st.mem d md
    exact loadDef_below hB e d he
  have below : ∀ d ∈ rds ++ fds ++ memDefs σ st.mem, d.Below vals.length := by
    intro d md
    simp only [List.mem_append] at md
    rcases md with (m | m) | m
    · exact rbelow d m
    · exact fbelow d m
    · exact mbelow d m
  have hext : extend vals (rds ++ fds ++ memDefs σ st.mem) =
      vals ++ (rds ++ fds ++ memDefs σ st.mem).map (Def.eval vals) := by
    simpa using extend_pre vals (rds ++ fds ++ memDefs σ st.mem) [] (by simpa using below)
  rw [hext]
  have hlen : (vals ++ (rds ++ fds ++ memDefs σ st.mem).map (Def.eval vals)).length =
      vals.length + (rds.length + fds.length + (memDefs σ st.mem).length) := by
    simp [Nat.add_assoc]
  rw [hlen]
  have segR : ∀ (j : Nat) (d : Def), rds[j]? = some d → (rds ++ fds ++ memDefs σ st.mem)[j]? = some d := by
    intro j d h
    rw [List.append_assoc, List.getElem?_append_left (lt_of_getElem?_some rds j d h), h]
  have segF : ∀ (t : Nat) (d : Def), fds[t]? = some d →
      (rds ++ fds ++ memDefs σ st.mem)[rds.length + t]? = some d := by
    intro t d h
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_append_left (lt_of_getElem?_some fds t d h), h]
  have segM : ∀ (t : Nat) (d : Def), (memDefs σ st.mem)[t]? = some d →
      (rds ++ fds ++ memDefs σ st.mem)[rds.length + fds.length + t]? = some d := by
    intro t d h
    rw [List.getElem?_append_right (by simp), List.length_append, Nat.add_sub_cancel_left, h]
  -- the register value via VHolds
  have viaRegs : ∀ r i, regMap σ vals.length st.us r = some i →
      regVal y r = (vals ++ (rds ++ fds ++ memDefs σ st.mem).map (Def.eval vals)).getD i 0 := by
    intro r i h
    have hv1 := hv.1 r
    change (match lookupUpd st.us r with
      | none => regVal y r = regVal x r
      | some none => True
      | some (some u) => regVal y r = u.eval x) at hv1
    rcases regMap_spec σ st.us vals.length rds hr r i h with ⟨hn, hs⟩ | ⟨u, d, j, hu, hd, hj, rfl⟩
    · rw [hn] at hv1
      rw [hv1, hA.1 r i hs, getD_left _ _ _ (hB.1 r i hs)]
    · rw [hu] at hv1
      rw [hv1, getD_right, getD_map_of vals _ _ _ (segR j d hj), (defOf_sound hA hB u d hd).1]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  -- registers
  · intro r i h
    simp only at h
    split at h
    · next x0 hmm =>
      subst h
      obtain ⟨e, d, j, me, her, hed, hj, rfl⟩ := memMap_spec σ st.mem _ r i hmm
      rw [show vals.length + rds.length + fds.length + j = vals.length + (rds.length + fds.length + j) by omega,
        getD_right, getD_map_of vals _ _ _ (segM j d hj)]
      exact (loadDef_sound hcoh hA hm e me r her d hed).symm
    · exact viaRegs r i h
  -- flags
  · intro n z c v h
    simp only at h
    cases hfl : st.fl with
    | none =>
      rw [hfl] at h
      have hv2 := hv.2
      rw [hfl] at hv2
      obtain ⟨h0, h1, h2, h3⟩ := hA.2.1 n z c v h
      obtain ⟨b0, b1, b2, b3⟩ := hB.2.1 n z c v h
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [getD_left _ _ _ b0, ← h0]; exact hv2 0
      · rw [getD_left _ _ _ b1, ← h1]; exact hv2 1
      · rw [getD_left _ _ _ b2, ← h2]; exact hv2 2
      · rw [getD_left _ _ _ b3, ← h3]; exact hv2 3
    | some q =>
      obtain ⟨a, b, cc, d⟩ := q
      rw [hfl] at h hf
      have hv2 := hv.2
      rw [hfl] at hv2
      obtain ⟨a', b', c', d', rfl, ea, eb, ec, ed, -, -, -, -⟩ := flagDefs_spec hA hB a b cc d fds hf
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨f0, f1, f2, f3⟩ := hv2
      refine ⟨?_, ?_, ?_, ?_⟩
      · have e0 := segF 0 a' rfl
        rw [Nat.add_zero] at e0
        rw [getD_right, getD_map_of vals _ _ _ e0, ea]; exact f0
      · rw [Nat.add_assoc, getD_right, getD_map_of vals _ _ _ (segF 1 b' rfl), eb]; exact f1
      · rw [Nat.add_assoc, getD_right, getD_map_of vals _ _ _ (segF 2 c' rfl), ec]; exact f2
      · rw [Nat.add_assoc, getD_right, getD_map_of vals _ _ _ (segF 3 d' rfl), ed]; exact f3
  -- memory bytes
  · intro g j i k h
    simp only at h
    split at h
    · next rt hs =>
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨i', hi', rfl, rfl⟩ := h
      have hstore := hm.1 _ (storebOf_mem st.mem g j rt hs)
      simp only at hstore
      rw [hstore, hA.1 rt i' hi', getD_left _ _ _ (hB.1 rt i' hi')]
      simp
    · next hsb =>
      split at h
      · next rt hs =>
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨i', hi', rfl, rfl⟩ := h
        have hw := hm.1 _ (storeOf_mem st.mem g (j / 8) rt hs)
        simp only at hw
        have c := hcoh y g (j / 8) (regVal x rt) hw (j % 8) (Nat.mod_lt _ (by omega))
        rw [Nat.div_add_mod] at c
        rw [c, hA.1 rt i' hi', getD_left _ _ _ (hB.1 rt i' hi')]
      · next hs =>
        split at h
        · next rt t h32 =>
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
          obtain ⟨i', hi', rfl, rfl⟩ := h
          obtain ⟨j', m32, rfl, ht⟩ := store32Of_mem st.mem g j rt t h32
          have hst := hm.1 _ m32
          simp only at hst
          rw [hst t ht, hA.1 rt i' hi', getD_left _ _ _ (hB.1 rt i' hi')]
        · next h32 =>
          split at h
          · next hc =>
            rw [hm.2.2 g hc.1 j hc.2 (storebOf_none st.mem g j hsb) (storeOf_none st.mem g (j / 8) hs)
                (store32Of_none st.mem g j h32),
              hA.2.2 g j i k h, getD_left _ _ _ (hB.2.2 g j i k h)]
          · cases h
  -- bounded: registers
  · intro r i h
    simp only at h
    split at h
    · next x0 hmm =>
      subst h
      obtain ⟨e, d, j, -, -, -, hj, rfl⟩ := memMap_spec σ st.mem _ r i hmm
      have := lt_of_getElem?_some _ j d hj
      omega
    · rcases regMap_spec σ st.us vals.length rds hr r i h with ⟨_, hs⟩ | ⟨u, d, j, _, _, hj, rfl⟩
      · have := hB.1 r i hs; omega
      · have := lt_of_getElem?_some rds j d hj; omega
  -- bounded: flags
  · intro a b c d h
    simp only at h
    cases hfl : st.fl with
    | none =>
      rw [hfl] at h
      obtain ⟨h0, h1, h2, h3⟩ := hB.2.1 a b c d h
      omega
    | some q =>
      obtain ⟨a0, b0, c0, d0⟩ := q
      rw [hfl] at h hf
      obtain ⟨a', b', c', d', rfl, -⟩ := flagDefs_spec hA hB a0 b0 c0 d0 fds hf
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp only [List.length_cons, List.length_nil]
      omega
  -- bounded: memory bytes
  · intro g j i k h
    simp only at h
    split at h
    · next rt _ =>
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨i', hi', rfl, rfl⟩ := h
      have := hB.1 rt i' hi'; omega
    · split at h
      · next rt _ =>
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨i', hi', rfl, rfl⟩ := h
        have := hB.1 rt i' hi'; omega
      · split at h
        · next rt t _ =>
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
          obtain ⟨i', hi', rfl, rfl⟩ := h
          have := hB.1 rt i' hi'; omega
        · split at h
          · have := hB.2.2 g j i k h; omega
          · cases h

#print axioms step_agrees

end ArmCertValue
