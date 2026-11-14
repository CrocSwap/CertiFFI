import TranslateMem.WalkInj

/-! The shim slot in the injectivity argument: the 16-byte shim slot at the PA of SP = pins.sp
never shares a physical byte with the 32 input bytes. Exactly Memory's ShimFrameV premise `slotSep`, stated at the
slot's access-start PA + i (the hardware access), so no linearity premise is needed on the slot side.
From: the input bytes keep their in-page offset (`byte_offset`: E17 at the access starts + DataBytesLinear), the slot
start is a leaf output address (`slotLeaf`: E17 at the shim's STP/LDP access start, as `AccessLeaf`), sp 16-aligned (the
slot stays in one page), no double mmap on these pages (`NoDoubleMapSlot`, the d195 deployment premise extended to the
slot) and the caller's disjointness of the slot from [x1, x1+32) (from the [SP−80, SP) shim-entry statement). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TranslateMem
open ArmCertValue ArmCertValue.HeapV2Mem ArmCert.Translate.Model

/-- Memory's RtShim2.ShimMem.slotBytes, restated: PA a lies in the 16-byte slot at the PA of SP. -/
def SlotBytes (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (a : Nat) : Prop :=
  ∃ n, mapping (BitVec.ofNat 64 p.sp) = some n ∧ n ≤ a ∧ a < n + 16

/-- E17 at the shim slot's access start: the mapping there is a leaf output address. -/
def SlotLeaf (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) : Prop :=
  ∃ l : Leaf, mapping (BitVec.ofNat 64 p.sp) = some (leafPA (BitVec.ofNat 64 p.sp) l)

/-- DEPLOYMENT (no double mmap, d195), extended to the slot: an input byte and the slot start sharing a frame share a
    VA page. -/
def NoDoubleMapSlot (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) : Prop :=
  ∀ j, j < 32 → ∀ q n, mapping (BitVec.ofNat 64 (p.x1 + j)) = some q → mapping (BitVec.ofNat 64 p.sp) = some n →
    q / 4096 = n / 4096 → (p.x1 + j) / 4096 = p.sp / 4096

theorem slotSep_of_walk (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) (hd : RegionsDisjoint p)
    (aligned : p.sp % 16 = 0 ∧ p.x0 % 16 = 0 ∧ p.x1 % 16 = 0) (walk : AccessLeaf p mapping)
    (dbl : DataBytesLinear p mapping) (slot : SlotLeaf p mapping) (nd : NoDoubleMapSlot p mapping)
    (slotDisj : p.x1 + 32 ≤ p.sp ∨ p.sp + 16 ≤ p.x1) (spHi : p.sp + 16 ≤ 2 ^ 64) :
    ∀ j, j < 32 → ∀ q, mapping (BitVec.ofNat 64 (p.x1 + j)) = some q → ¬ SlotBytes p mapping q := by
  intro j hj q hq ⟨n, hn, lo, hi⟩
  obtain ⟨b0, b1, b2, b3, d1, d2, d3⟩ := hd
  -- the input byte keeps its in-page offset
  have mem : (HeapV2Plan.I, j) ∈ heapv2Bytes := by
    simp only [heapv2Bytes, regions, HeapV2Plan.regions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨j, by simpa [HeapV2Plan.I] using hj, rfl⟩
  obtain ⟨q', hq', oq⟩ := byte_offset p mapping ⟨b0, b1, b2, b3, d1, d2, d3⟩ aligned walk dbl _ mem
  have hva : byteVA p HeapV2Plan.I j = BitVec.ofNat 64 (p.x1 + j) := by
    apply BitVec.eq_of_toNat_eq
    rw [byteVA_toNat p _ j _ rfl (by simp [HeapV2Plan.I, pinv, HeapV2E17.pin]; omega)
      (by simp [HeapV2Plan.I, pinv, HeapV2E17.pin]; omega)]
    simp [HeapV2Plan.I, pinv, HeapV2E17.pin, BitVec.toNat_ofNat]; omega
  simp only [hva] at hq' oq
  rw [hq] at hq'; cases hq'
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show p.x1 + j < 2 ^ 64 by omega)] at oq
  -- the slot start keeps its offset, and the 16-aligned slot stays in its page
  obtain ⟨l, hl⟩ := slot
  have en : n = leafPA (BitVec.ofNat 64 p.sp) l := by rw [hn] at hl; exact Option.some.inj hl
  have on := leafPA_mod (BitVec.ofNat 64 p.sp) l
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show p.sp < 2 ^ 64 by omega), ← en] at on
  have sameFrame : q / 4096 = n / 4096 := by
    have := Nat.div_add_mod q 4096; have := Nat.div_add_mod n 4096
    have : p.sp % 4096 + 16 ≤ 4096 := by omega
    omega
  have page := nd j hj q n hq hn sameFrame
  have := Nat.div_add_mod (p.x1 + j) 4096; have := Nat.div_add_mod p.sp 4096
  have := Nat.div_add_mod q 4096; have := Nat.div_add_mod n 4096
  omega

#print axioms slotSep_of_walk
end TranslateMem
