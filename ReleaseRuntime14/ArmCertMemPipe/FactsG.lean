-- Memory ((c), d200): the per-step access facts of the runtime14 memory routes from the chain's value-layer
-- Agrees (ArmCertPipe.AgreesAt). Loads: the accessed bytes are present because the regions' tracked bytes are (Agrees),
-- given the route's linear VAs; the static fields (mapped / not MMIO / outside the tables / aligned) and the consumer
-- map's permission come from the deployment and P1. Stores need no presence (their Facts are static + permission).
import HeapV2StepCerts.RegBindCore
import ArmCertPipe.Prefix
import ArmCertMemPipe.TailLdrU64
import ArmCertMemPipe.TailLdrU64Sp
import ArmCertMemPipe.TailLdrU32
import ArmCertMemPipe.TailLdrbU
import ArmCertMemPipe.TailLdpPost
import ArmCertMemPipe.TailLdpOff
open Sail ArmFull ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
set_option autoImplicit false
namespace ArmCertMemPipe.FactsG
open ArmCertValue ArmBridge.Draft

/-- A tracked region byte is present at its PA. -/
theorem present_of_agrees {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {vals : List (BitVec 64)} {σ : Sym}
    {x : NativeState} (h : Agrees mapping pinv vals σ x) {r : Region} {j i k : Nat} (hb : σ.memB r j = some (i, k))
    {q : Nat} (hq : mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + (j : Int))) = some q) : (x.mem[q]?).isSome := by
  have e := h.2.2 r j i k hb
  unfold regionByte at e
  rw [hq, Option.bind_some] at e
  rw [e]; rfl

/-- n consecutive tracked bytes j0.. of r, linearly mapped onto pa.., give an n-byte datum at pa. -/
theorem bytes_of_agrees {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {vals : List (BitVec 64)} {σ : Sym}
    {x : NativeState} (h : Agrees mapping pinv vals σ x) (r : Region) (j0 n pa : Nat)
    (lin : ∀ t : Nat, t < n → mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + ((j0 + t : Nat) : Int))) = some (pa + t))
    (cov : ∀ t : Nat, t < n → ∃ i k, σ.memB r (j0 + t) = some (i, k)) :
    ∃ v : BitVec (8 * n), ∀ t < n, x.mem[pa + t]? = some (v.extractLsb' (8 * t) 8) :=
  HeapV2StepCerts.C3.exists_value (fun t => x.mem[pa + t]?) n (fun t ht => by
    obtain ⟨i, k, hb⟩ := cov t ht
    exact present_of_agrees h hb (lin t ht))

/-- The same from AgreesAt (the runtime14 chain extra) at step k. -/
theorem bytes_of_agreesAt {mapping : BitVec 64 → Option Nat} {pinv : Nat → Nat} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List StepV} {k : Nat} {x : NativeState}
    (h : ArmCertPipe.AgreesAt mapping pinv regions σ0 inputs plan k x) (r : Region) (j0 n pa : Nat)
    (lin : ∀ t : Nat, t < n → mapping (BitVec.ofInt 64 ((pinv r.pin : Int) + r.off + ((j0 + t : Nat) : Int))) = some (pa + t))
    (cov : ∀ ds σ, compileRun regions σ0 inputs.length (plan.take k) = some (ds, σ) →
      ∀ t : Nat, t < n → ∃ i k', σ.memB r (j0 + t) = some (i, k')) :
    ∃ v : BitVec (8 * n), ∀ t < n, x.mem[pa + t]? = some (v.extractLsb' (8 * t) 8) := by
  obtain ⟨ds, σ, hc, ha, _⟩ := h
  exact bytes_of_agrees ha r j0 n pa lin (cov ds σ hc)

/-! Facts constructors for the load forms (the static / permission fields are the caller's). -/

theorem facts_LdrU64 {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {imm12 : BitVec 12} {Rn : BitVec 5} {x : NativeState} (pa : BitVec 56)
    (mapped : mapping (MemClass.LdrU64.addr x Rn imm12) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (outside : ¬ (rowsFootprint spec.imageRows).byte pa.toNat) (align : (MemClass.LdrU64.addr x Rn imm12).toNat % 8 = 0)
    (bytes : ∃ v : BitVec (8 * 8), ∀ t < 8, x.mem[pa.toNat + t]? = some (v.extractLsb' (8 * t) 8))
    (perm : ∀ acc, ArmCert.Translate.Model.DataShape false acc → m.permitted (MemClass.LdrU64.addr x Rn imm12) acc true ((8 : Nat) : Int)) :
    LdrU64.Facts spec config rows mapping m imm12 Rn x :=
  ⟨pa, mapped, mmio, outside, align, bytes, perm⟩

theorem facts_LdrU32 {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {imm12 : BitVec 12} {Rn : BitVec 5} {x : NativeState} (pa : BitVec 56)
    (mapped : mapping (MemClass.LdrU32.addr x Rn imm12) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (outside : ¬ (rowsFootprint spec.imageRows).byte pa.toNat) (align : (MemClass.LdrU32.addr x Rn imm12).toNat % 4 = 0)
    (bytes : ∃ v : BitVec (4 * 8), ∀ t < 4, x.mem[pa.toNat + t]? = some (v.extractLsb' (8 * t) 8))
    (perm : ∀ acc, ArmCert.Translate.Model.DataShape false acc → m.permitted (MemClass.LdrU32.addr x Rn imm12) acc true ((4 : Nat) : Int)) :
    LdrU32.Facts spec config rows mapping m imm12 Rn x :=
  ⟨pa, mapped, mmio, outside, align, bytes, perm⟩

theorem facts_LdrbU {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {imm12 : BitVec 12} {Rn : BitVec 5} {x : NativeState} (pa : BitVec 56)
    (mapped : mapping (MemClass.LdrbU.addr x Rn imm12) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (outside : ¬ (rowsFootprint spec.imageRows).byte pa.toNat)
    (bytes : ∃ v : BitVec (1 * 8), ∀ t < 1, x.mem[pa.toNat + t]? = some (v.extractLsb' (8 * t) 8))
    (perm : ∀ acc, ArmCert.Translate.Model.DataShape false acc → m.permitted (MemClass.LdrbU.addr x Rn imm12) acc true ((1 : Nat) : Int)) :
    LdrbU.Facts spec config rows mapping m imm12 Rn x :=
  ⟨pa, mapped, mmio, outside, bytes, perm⟩

theorem facts_LdrU64Sp {domain : QueryDomain} {spec : TopologyImageSpec domain} {config : AttributeConfig}
    {rows : List PermissionRow} {mapping : BitVec 64 → Option Nat} {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {imm12 : BitVec 12} {x : NativeState} (hsp : x.regs.SP_EL0.toNat % 16 = 0) (pa : BitVec 56)
    (mapped : mapping (MemClass.LdrU64Sp.addr x imm12) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (outside : ¬ (rowsFootprint spec.imageRows).byte pa.toNat) (align : (MemClass.LdrU64Sp.addr x imm12).toNat % 8 = 0)
    (bytes : ∃ v : BitVec (8 * 8), ∀ t < 8, x.mem[pa.toNat + t]? = some (v.extractLsb' (8 * t) 8))
    (perm : ∀ acc, ArmCert.Translate.Model.DataShape false acc → m.permitted (MemClass.LdrU64Sp.addr x imm12) acc true ((8 : Nat) : Int)) :
    LdrU64Sp.Facts spec config rows mapping m imm12 x :=
  ⟨hsp, pa, mapped, mmio, outside, align, bytes, perm⟩

theorem facts_LdpPost {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {mapping : BitVec 64 → Option Nat} {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {x : NativeState} (hsp : x.regs.SP_EL0.toNat % 16 = 0) (pa : BitVec 56)
    (mapped : mapping x.regs.SP_EL0 = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (bytes : ∃ v : BitVec 128, ∀ t < 16, x.mem[pa.toNat + t]? = some ((v : BitVec (16 * 8)).extractLsb' (8 * t) 8))
    (perm : ∀ acc, ArmCert.Translate.Model.DataShape false acc → m.permitted x.regs.SP_EL0 acc true ((16 : Nat) : Int)) :
    LdpPost.Facts spec mapping m x :=
  ⟨hsp, pa, mapped, mmio, bytes, perm⟩

theorem facts_LdpOff {domain : QueryDomain} {spec : TopologyImageSpec domain}
    {mapping : BitVec 64 → Option Nat} {m : ArmCert.Premises.TranslationAgreesV1.ConsumerMap}
    {imm7 : BitVec 7} {x : NativeState} (hsp : x.regs.SP_EL0.toNat % 16 = 0)
    (half : (ArmCertMem.LdpEval.ldpAddr x imm7).toNat % 16 = 0) (pa : BitVec 56)
    (mapped : mapping (ArmCertMem.LdpEval.ldpAddr x imm7) = some pa.toNat) (mmio : MemM1.MemReadIF.NotMMIO pa)
    (bytes : ∃ v : BitVec 128, ∀ t < 16, x.mem[pa.toNat + t]? = some ((v : BitVec (16 * 8)).extractLsb' (8 * t) 8))
    (perm : ∀ acc, ArmCert.Translate.Model.DataShape false acc → m.permitted (ArmCertMem.LdpEval.ldpAddr x imm7) acc true ((16 : Nat) : Int)) :
    LdpOff.Facts spec mapping m imm7 x :=
  ⟨hsp, half, pa, mapped, mmio, bytes, perm⟩

#print axioms present_of_agrees
#print axioms bytes_of_agreesAt
#print axioms facts_LdrU64
#print axioms facts_LdpOff
end ArmCertMemPipe.FactsG
