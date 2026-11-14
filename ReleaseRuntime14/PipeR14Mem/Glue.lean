-- Memory (d200 P3 memory steps): small generic lemmas the generated runtime14 memory step facts use.
import PipeR14Mem.Static
import ArmCertR14.Value
set_option autoImplicit false
namespace PipeR14
open ArmCertValue

theorem pinv_of (p : R14E17.Pins) (i : Nat) (h32 : i ≠ 32) (h33 : i ≠ 33) : pinv p i = p.regs i := by
  simp [pinv, h32, h33]
theorem pinv_32 (p : R14E17.Pins) : pinv p 32 = p.indirect "x0+mem64[x1+8]+24" := rfl
theorem pinv_33 (p : R14E17.Pins) : pinv p 33 = p.indirect "x0+UBFM64[1,63](x1)+24" := by simp [pinv]

theorem addrK0 (a : Nat) : BitVec.ofNat 64 a = BitVec.ofInt 64 ((a : Int) + 0) := by
  rw [Int.add_zero, BitVec.ofInt_natCast]
theorem addrK1 (a : Nat) (c : Int) (k : BitVec 64) (hk : k = BitVec.ofInt 64 c) :
    BitVec.ofNat 64 a + k = BitVec.ofInt 64 ((a : Int) + c) := by
  rw [hk, BitVec.ofInt_add, BitVec.ofInt_natCast]
theorem addrK2 (a : Nat) (c : Int) (k1 k2 : BitVec 64) (hk : k1 + k2 = BitVec.ofInt 64 c) :
    BitVec.ofNat 64 a + k1 + k2 = BitVec.ofInt 64 ((a : Int) + c) := by
  rw [BitVec.add_assoc, hk, BitVec.ofInt_add, BitVec.ofInt_natCast]

theorem ofInt_toNat (v : BitVec 64) : BitVec.ofInt 64 ((v.toNat : Nat) : Int) = v := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem sp16_of (a : Nat) (k : BitVec 64) (ha : a % 16 = 0) (hk : k.toNat % 16 = 0) :
    (BitVec.ofNat 64 a + k).toNat % 16 = 0 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
theorem sp16_of0 (a : Nat) (ha : a % 16 = 0) : (BitVec.ofNat 64 a).toNat % 16 = 0 := by
  simp only [BitVec.toNat_ofNat]; omega

open ArmCertR14.Value in
theorem bf_store32 {rt : HeapV2StepCerts.RegBind.Reg} {r r' : Region} {j j' : Nat}
    (h : ByteFree [.store32 rt r j] r' j') : ¬ (r' = r ∧ j ≤ j' ∧ j' < j + 4) := by
  rintro ⟨rfl, lo, hi⟩; exact h.2.2 rt j (List.mem_singleton.2 rfl) ⟨lo, hi⟩
open ArmCertR14.Value in
theorem bf_store {rt : HeapV2StepCerts.RegBind.Reg} {r r' : Region} {w j' : Nat}
    (h : ByteFree [.store rt r w] r' j') : ¬ (r' = r ∧ 8 * w ≤ j' ∧ j' < 8 * w + 8) := by
  rintro ⟨rfl, lo, hi⟩
  have e : j' / 8 = w := by omega
  exact h.2.1 rt (by rw [e]; exact List.mem_singleton.2 rfl)
open ArmCertR14.Value in
theorem bf_storeb {rt : HeapV2StepCerts.RegBind.Reg} {r r' : Region} {j j' : Nat}
    (h : ByteFree [.storeb rt r j] r' j') : ¬ (r' = r ∧ j ≤ j' ∧ j' < j + 1) := by
  rintro ⟨rfl, lo, hi⟩
  have e : j' = j := by omega
  exact h.1 rt (by rw [e]; exact List.mem_singleton.2 rfl)
open ArmCertR14.Value in
theorem bf_pair {rt rt2 : HeapV2StepCerts.RegBind.Reg} {r r' : Region} {w j' : Nat}
    (h : ByteFree [.store rt r w, .store rt2 r (w + 1)] r' j') : ¬ (r' = r ∧ 8 * w ≤ j' ∧ j' < 8 * w + 16) := by
  rintro ⟨rfl, lo, hi⟩
  by_cases hw : j' < 8 * w + 8
  · have e : j' / 8 = w := by omega
    exact h.2.1 rt (by rw [e]; simp)
  · have e : j' / 8 = w + 1 := by omega
    exact h.2.1 rt2 (by rw [e]; simp)

open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk in
/-- ChainInvG reads `offset` only at k (the pc field): it transports to any offset agreeing at k. Used by final plan
steps, whose next PC is not a plan offset. -/
theorem chainInvG_offset {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {scope : Nat → Prop} {image : MemReloc.Image} {loadBase : MemReloc.Word} {base : BitVec 64}
    {offset offset' : Nat → BitVec 64} {budget : Nat} {extra : Nat → ArmBridge.Draft.NativeState → Prop} {k : Nat}
    {x : ArmBridge.Draft.NativeState} (h : offset' k = offset k)
    (inv : ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset budget extra k x) :
    ArmCertPipe.ChainInvG spec config rows mapping m scope image loadBase base offset' budget extra k x :=
  { inv with v2 := { inv.v2 with v1 := { inv.v2.v1 with pc := by rw [h]; exact inv.v2.v1.pc } } }

end PipeR14
