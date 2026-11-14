-- Memory: MemVHolds for the heap-v2 memory classes (byte / pair, load / store), from the
-- payload rich steps' R (Pay + write frame) and the deployment premises DataBytesLinear / RegionsInjective.
import ArmCertValueMem.Classes
import HeapV2StepCerts.C3Core
import ArmCertValue.PhysicalMemory
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ArmCertValue.HeapV2Mem.Physical
open ArmCertValue ArmCertValue.MemRegion ArmCert.Translate.Model
open HeapV2StepCerts.RegBind (St regVal Reg)

/-- STRB: one byte store into region byte (r, j). -/
theorem memV_storeb (mapping : BitVec 64 → Option Nat) (bytePA : ArmCertValue.Physical.BytePA) (p : HeapV2E17.Pins) (x y : St)
    {e : Nat × Nat × Int × Nat × Bool} (hsz : e.2.2.2.1 = 1)
    (Rt : BitVec 5) (rt : Reg) (hrt : rt = .x (HeapV2StepCerts.RegBind.rk Rt))
    (r : Region) (j : Nat) (hr : r ∈ regions) (hj : j < 8 * r.words)
    (view : bytePA r j = mapping (HeapV2E17.dataVA p e)) (mapped : ∃ n, mapping (HeapV2E17.dataVA p e) = some n)
    (pay : HeapV2StepCerts.ValuePay.PayStrb p mapping e Rt x y)
    (written : Nat → Prop) (wo : ArmCert.Translate.WritesOnly written (fun a => x.mem[a]?) (fun a => y.mem[a]?))
    (inD : ∀ m, written m → RtSaved.accPA p mapping e m) (inj : ArmCertValue.Physical.RegionsInjective bytePA regions) :
    ArmCertValue.Physical.MemVHolds bytePA regions [MemEff.storeb rt r j] x y := by
  obtain ⟨n, hn⟩ := mapped
  have stored : ∀ b, b ∈ [(r, j)] → b ∈ heapv2Bytes := by
    intro b hb; simp only [List.mem_singleton] at hb; subst hb; exact mem_heapv2Bytes hr hj
  have cover : ∀ m, written m → ∃ b, b ∈ [(r, j)] ∧ bytePA b.1 b.2 = some m := by
    intro m hw
    rcases inD m hw with ⟨n', hn', h1, h2⟩ | ⟨h16, _⟩
    · rw [hsz] at h2
      refine ⟨(r, j), List.mem_singleton.2 rfl, ?_⟩
      show bytePA r j = some m
      rw [view, hn']; congr 1; omega
    · rw [hsz] at h16; cases h16
  have fr := ArmCertValue.Physical.frame_of_cover bytePA regions x y written wo [(r, j)] cover inj stored
  refine ⟨?_, ?_, ?_⟩
  · intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    show ArmCertValue.Physical.regionByte bytePA y r j = some ((regVal x rt).setWidth 8)
    rw [ArmCertValue.Physical.regionByte, view, hn, Option.bind_some, pay n hn, hrt]
    rfl
  · intro r' _ w hw _ hb _
    apply ArmCertValue.Physical.regionWord_congr
    intro k hk
    apply fr r' (8 * w + k) (mem_heapv2Bytes ‹r' ∈ regions› (by omega))
    intro hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hb rt (8 * w + k) (List.mem_singleton.2 rfl) (by omega)
  · intro r' hr' j' hj' hb _ _
    apply fr r' j' (mem_heapv2Bytes hr' hj')
    intro hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hb rt (List.mem_singleton.2 rfl)

#print axioms memV_storeb

/-- LDRB: one byte load from region byte (r, j); loads write no memory. -/
theorem memV_loadb (mapping : BitVec 64 → Option Nat) (bytePA : ArmCertValue.Physical.BytePA) (p : HeapV2E17.Pins) (x y : St)
    {e : Nat × Nat × Int × Nat × Bool}
    (Rt : BitVec 5) (rt : Reg) (hrt : rt = .x (HeapV2StepCerts.RegBind.rk Rt))
    (r : Region) (j : Nat) (view : bytePA r j = mapping (HeapV2E17.dataVA p e))
    (mapped : ∃ n, mapping (HeapV2E17.dataVA p e) = some n)
    (pres : ∀ n, mapping (HeapV2E17.dataVA p e) = some n → (x.mem[n]?).isSome)
    (pay : HeapV2StepCerts.ValuePay.PayLdrb p mapping e Rt x y)
    (written : Nat → Prop) (wo : ArmCert.Translate.WritesOnly written (fun a => x.mem[a]?) (fun a => y.mem[a]?))
    (none : ∀ m, written m → False) (inj : ArmCertValue.Physical.RegionsInjective bytePA regions) :
    ArmCertValue.Physical.MemVHolds bytePA regions [MemEff.loadb rt r j] x y := by
  obtain ⟨n, hn⟩ := mapped
  have fr := ArmCertValue.Physical.frame_of_cover bytePA regions x y written wo [] (fun m hw => (none m hw).elim) inj (fun b hb => by cases hb)
  refine ⟨?_, ?_, ?_⟩
  · intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (pres n hn)
    refine ⟨b, ?_, ?_⟩
    · rw [ArmCertValue.Physical.regionByte, view, hn, Option.bind_some, hb]
    · rw [hrt]; show y.regs.gpr[(HeapV2StepCerts.RegBind.rk Rt).val] = _
      rw [pay n hn b hb, ldrbVal_eq]
  · intro r' hr' w hw _ _ _
    exact ArmCertValue.Physical.regionWord_congr _ _ _ _ _ (fun k hk => fr r' (8 * w + k) (mem_heapv2Bytes hr' (by omega)) (by simp))
  · intro r' hr' j' hj' _ _ _
    exact fr r' j' (mem_heapv2Bytes hr' hj') (by simp)

theorem plus8_ofInt (x : Int) : ArmCertWalk.plus8 (BitVec.ofInt 64 x) = BitVec.ofInt 64 (x + 8) := by
  simp only [ArmCertWalk.plus8, Sail.BitVec.addInt]
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_ofInt, BitVec.toInt_add]
  try omega

#print axioms memV_loadb
#print axioms plus8_ofInt

/-- Layout of a 16-byte pair access on region words w, w+1. -/
theorem pair_layout (p : HeapV2E17.Pins) (r : Region) (w : Nat) (e : Nat × Nat × Int × Nat × Bool)
    (hpin : r.pin = e.2.1) (hoff : r.off + 8 * (w : Int) = e.2.2.1) (i : Nat) :
    byteVA p r (8 * w + i) = BitVec.ofInt 64 ((HeapV2E17.pin p e.2.1 : Int) + e.2.2.1 + i) := by
  unfold byteVA pinv; rw [← hpin, ← hoff]; congr 1; simp only [Int.natCast_add, Int.natCast_mul]; omega

/-- STP / STP8: two word stores into region words w, w+1 (X[Rt] then X[Rt2]). -/
theorem memV_storePair (mapping : BitVec 64 → Option Nat) (bytePA : ArmCertValue.Physical.BytePA) (p : HeapV2E17.Pins) (x y : St)
    {e : Nat × Nat × Int × Nat × Bool} (he : e ∈ HeapV2Plan.symbolicAccesses) (hsz : e.2.2.2.1 = 16)
    (Rt Rt2 : BitVec 5) (rt rt2 : Reg) (hrt : rt = .x (HeapV2StepCerts.RegBind.rk Rt))
    (hrt2 : rt2 = .x (HeapV2StepCerts.RegBind.rk Rt2))
    (r : Region) (w : Nat) (hr : r ∈ regions) (hw : w + 1 < r.words)
    (hpin : r.pin = e.2.1) (hoff : r.off + 8 * (w : Int) = e.2.2.1)
    (view : ∀ i, i < 16 → bytePA r (8 * w + i) = (mapping (HeapV2E17.dataVA p e)).map (· + i)) (mapped : ∃ n, mapping (HeapV2E17.dataVA p e) = some n)
    (upper : ∀ n, mapping (HeapV2E17.dataVA p e) = some n → mapping (ArmCertWalk.plus8 (HeapV2E17.dataVA p e)) = some (n + 8))
    (pay : RtSaved.MemFacts.StpPay p mapping e Rt Rt2 x y)
    (written : Nat → Prop) (wo : ArmCert.Translate.WritesOnly written (fun a => x.mem[a]?) (fun a => y.mem[a]?))
    (inD : ∀ m, written m → RtSaved.accPA p mapping e m) (inj : ArmCertValue.Physical.RegionsInjective bytePA regions) :
    ArmCertValue.Physical.MemVHolds bytePA regions [MemEff.store rt r w, MemEff.store rt2 r (w + 1)] x y := by
  obtain ⟨n, hn⟩ := mapped
  have lay := pair_layout p r w e hpin hoff
  have lin : ∀ i, i < 16 → bytePA r (8 * w + i) = some (n + i) := by
    intro i hi
    rw [view i hi, hn]; rfl
  have hva0 : HeapV2E17.dataVA p e = byteVA p r (8 * w + 0) := by rw [lay 0]; simp [HeapV2E17.dataVA]
  let stored : List (Region × Nat) := (List.range 16).map fun i => (r, 8 * w + i)
  have hst : ∀ b, b ∈ stored → b ∈ heapv2Bytes := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact mem_heapv2Bytes hr (by have := List.mem_range.1 hi; omega)
  have cover : ∀ m, written m → ∃ b, b ∈ stored ∧ bytePA b.1 b.2 = some m := by
    intro m hw'
    rcases inD m hw' with ⟨n', hn', h1, h2⟩ | ⟨_, n'', hn'', h1, h2⟩
    · rw [hn] at hn'; obtain rfl := Option.some.inj hn'
      rw [hsz] at h2
      refine ⟨(r, 8 * w + (m - n)), List.mem_map.2 ⟨m - n, List.mem_range.2 (by omega), rfl⟩, ?_⟩
      rw [lin (m - n) (by omega)]; congr 1; omega
    · have h8 : mapping (ArmCertWalk.plus8 (HeapV2E17.dataVA p e)) = some (n + 8) := upper n hn
      rw [h8] at hn''; obtain rfl := Option.some.inj hn''
      refine ⟨(r, 8 * w + (m - n)), List.mem_map.2 ⟨m - n, List.mem_range.2 (by omega), rfl⟩, ?_⟩
      rw [lin (m - n) (by omega)]; congr 1; omega
  have fr := ArmCertValue.Physical.frame_of_cover bytePA regions x y written wo stored cover inj hst
  have inS : ∀ r' j', (r', j') ∈ stored → r' = r ∧ (j' / 8 = w ∨ j' / 8 = w + 1) := by
    intro r' j' h
    obtain ⟨i, hi, he'⟩ := List.mem_map.1 h
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    have := List.mem_range.1 hi
    exact ⟨rfl, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e' he'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he'
    rcases he' with rfl | rfl
    · show ArmCertValue.Physical.regionWord bytePA y r w = some (regVal x rt)
      apply (ArmCertValue.Physical.regionWord_bytes _ _ _ _ _).2
      intro k hk
      rw [ArmCertValue.Physical.regionByte, lin k (by omega), Option.bind_some, pay n hn k (by omega), slotByte_lo _ _ k hk, hrt]
      rfl
    · show ArmCertValue.Physical.regionWord bytePA y r (w + 1) = some (regVal x rt2)
      apply (ArmCertValue.Physical.regionWord_bytes _ _ _ _ _).2
      intro k hk
      rw [show 8 * (w + 1) + k = 8 * w + (8 + k) by omega, ArmCertValue.Physical.regionByte, lin (8 + k) (by omega), Option.bind_some,
        pay n hn (8 + k) (by omega), slotByte_hi _ _ k hk, hrt2]
      rfl
  · intro r' hr' w' hw' hno _ _
    apply ArmCertValue.Physical.regionWord_congr
    intro k hk
    apply fr r' (8 * w' + k) (mem_heapv2Bytes hr' (by omega))
    intro hm
    obtain ⟨rfl, hj⟩ := inS r' _ hm
    rcases hj with hj | hj
    · exact hno rt (by rw [show w' = w by omega]; simp)
    · exact hno rt2 (by rw [show w' = w + 1 by omega]; simp)
  · intro r' hr' j' hj' _ hno _
    apply fr r' j' (mem_heapv2Bytes hr' hj')
    intro hm
    obtain ⟨rfl, hj⟩ := inS r' j' hm
    rcases hj with hj | hj
    · exact hno rt (by rw [hj]; simp)
    · exact hno rt2 (by rw [hj]; simp)

#print axioms memV_storePair

/-- LDP / LDP8: two word loads from region words w, w+1 (X[Rt] low, X[Rt2] high); loads write no memory. -/
theorem memV_loadPair (mapping : BitVec 64 → Option Nat) (bytePA : ArmCertValue.Physical.BytePA) (p : HeapV2E17.Pins) (x y : St)
    {e : Nat × Nat × Int × Nat × Bool} (he : e ∈ HeapV2Plan.symbolicAccesses) (hsz : e.2.2.2.1 = 16)
    (Rt Rt2 : BitVec 5) (rt rt2 : Reg) (hrt : rt = .x (HeapV2StepCerts.RegBind.rk Rt))
    (hrt2 : rt2 = .x (HeapV2StepCerts.RegBind.rk Rt2))
    (r : Region) (w : Nat) (hpin : r.pin = e.2.1) (hoff : r.off + 8 * (w : Int) = e.2.2.1)
    (view : ∀ i, i < 16 → bytePA r (8 * w + i) = (mapping (HeapV2E17.dataVA p e)).map (· + i)) (mapped : ∃ n, mapping (HeapV2E17.dataVA p e) = some n)
    (pres : ∀ n, mapping (HeapV2E17.dataVA p e) = some n → ∀ i, i < 16 → (x.mem[n + i]?).isSome)
    (pay : RtSaved3.MemFacts2.LdpPay2 p mapping e Rt Rt2 x y)
    (written : Nat → Prop) (wo : ArmCert.Translate.WritesOnly written (fun a => x.mem[a]?) (fun a => y.mem[a]?))
    (none : ∀ m, written m → False) (inj : ArmCertValue.Physical.RegionsInjective bytePA regions) :
    ArmCertValue.Physical.MemVHolds bytePA regions [MemEff.load rt r w, MemEff.load rt2 r (w + 1)] x y := by
  obtain ⟨n, hn⟩ := mapped
  have lay := pair_layout p r w e hpin hoff
  have lin : ∀ i, i < 16 → bytePA r (8 * w + i) = some (n + i) := by
    intro i hi
    rw [view i hi, hn]; rfl
  obtain ⟨d, hd⟩ := HeapV2StepCerts.C3.exists_value (fun i => x.mem[n + i]?) 16 (pres n hn)
  obtain ⟨hhi, hlo⟩ := pay n hn d hd
  have fr := ArmCertValue.Physical.frame_of_cover bytePA regions x y written wo [] (fun m hw => (none m hw).elim) inj (fun b hb => by cases hb)
  refine ⟨?_, ?_, ?_⟩
  · intro e' he'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he'
    rcases he' with rfl | rfl
    · show ArmCertValue.Physical.regionWord bytePA x r w = some (regVal y rt)
      rw [hrt]
      show ArmCertValue.Physical.regionWord bytePA x r w = some (y.regs.gpr[(HeapV2StepCerts.RegBind.rk Rt).val])
      rw [hlo]
      apply (ArmCertValue.Physical.regionWord_bytes _ _ _ _ _).2
      intro k hk
      rw [ArmCertValue.Physical.regionByte, lin k (by omega), Option.bind_some, hd k (by omega)]
      exact congrArg some (byteOf_ldpLo d k hk).symm
    · show ArmCertValue.Physical.regionWord bytePA x r (w + 1) = some (regVal y rt2)
      rw [hrt2]
      show ArmCertValue.Physical.regionWord bytePA x r (w + 1) = some (y.regs.gpr[(HeapV2StepCerts.RegBind.rk Rt2).val])
      rw [hhi]
      apply (ArmCertValue.Physical.regionWord_bytes _ _ _ _ _).2
      intro k hk
      rw [show 8 * (w + 1) + k = 8 * w + (8 + k) by omega, ArmCertValue.Physical.regionByte, lin (8 + k) (by omega), Option.bind_some,
        hd (8 + k) (by omega), show 8 + k = k + 8 by omega]
      exact congrArg some (byteOf_ldpHi d k hk).symm
  · intro r' hr' w' hw' _ _ _
    exact ArmCertValue.Physical.regionWord_congr _ _ _ _ _ (fun k hk => fr r' (8 * w' + k) (mem_heapv2Bytes hr' (by omega)) (by simp))
  · intro r' hr' j' hj' _ _ _
    exact fr r' j' (mem_heapv2Bytes hr' hj') (by simp)

#print axioms memV_loadPair

/-- Layout of a 1-byte access at region byte j. -/
theorem byte_layout (p : HeapV2E17.Pins) (r : Region) (j : Nat) (e : Nat × Nat × Int × Nat × Bool)
    (hpin : r.pin = e.2.1) (hoff : r.off + (j : Int) = e.2.2.1) : byteVA p r j = HeapV2E17.dataVA p e := by
  unfold byteVA pinv HeapV2E17.dataVA; rw [← hpin, ← hoff]; congr 1; omega

#print axioms byte_layout
end ArmCertValue.HeapV2Mem.Physical
