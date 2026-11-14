-- additive physical-byte value interface. Existing Core definitions remain intact.
-- A view identifies actual physical bytes; no translation of interior byte VAs occurs here.
import ArmCertValue.Core
set_option autoImplicit false
namespace ArmCertValue.Physical
open HeapV2StepCerts.RegBind (Reg St regVal)

abbrev BytePA := Region → Nat → Option Nat

def regionByte (bytePA : BytePA) (s : St) (r : Region) (j : Nat) : Option (BitVec 8) :=
  (bytePA r j).bind fun pa => s.mem[pa]?

def regionWord (bytePA : BytePA) (s : St) (r : Region) (w : Nat) : Option (BitVec 64) :=
  (List.range 8).foldr (fun k acc => do
    let byte ← regionByte bytePA s r (8 * w + k)
    let rest ← acc
    pure (rest ||| ((byte.setWidth 64) <<< (8 * k)))) (some 0#64)

/-- Each byte in a span uses one translation at the access start, then physical addition. -/
def spanPA (mapping : BitVec 64 → Option Nat) (start : BitVec 64) (j : Nat) : Option Nat :=
  (mapping start).map (· + j)

def Agrees (bytePA : BytePA) (vals : List (BitVec 64)) (σ : Sym)
    (s : St) : Prop :=
  (∀ r i, σ.regs r = some i → regVal s r = vals.getD i 0) ∧
  (∀ n z c v, σ.nzcv = some (n, z, c, v) →
    s.regs.PSTATE.N.setWidth 64 = vals.getD n 0 ∧ s.regs.PSTATE.Z.setWidth 64 = vals.getD z 0 ∧
    s.regs.PSTATE.C.setWidth 64 = vals.getD c 0 ∧ s.regs.PSTATE.V.setWidth 64 = vals.getD v 0) ∧
  (∀ r j i k, σ.memB r j = some (i, k) →
    regionByte bytePA s r j = some (((vals.getD i 0) >>> (8 * k)).setWidth 8))


def MemVHolds (bytePA : BytePA) (regions : List Region)
    (effs : List MemEff) (x y : St) : Prop :=
  (∀ e ∈ effs, match e with
    | .load rt r i => regionWord bytePA x r i = some (regVal y rt)
    | .store rt r i => regionWord bytePA y r i = some (regVal x rt)
    | .loadb rt r j => ∃ b, regionByte bytePA x r j = some b ∧ regVal y rt = b.setWidth 64
    | .storeb rt r j => regionByte bytePA y r j = some ((regVal x rt).setWidth 8)
    | .load32 rt r j => ∃ u : BitVec 64, u.toNat < 2 ^ 32 ∧
        (∀ t, t < 4 → regionByte bytePA x r (j + t) = some ((u >>> (8 * t)).setWidth 8)) ∧ regVal y rt = u
    | .store32 rt r j => ∀ t, t < 4 → regionByte bytePA y r (j + t) = some ((regVal x rt >>> (8 * t)).setWidth 8)) ∧
  (∀ r ∈ regions, ∀ w, w < r.words → (∀ rt, MemEff.store rt r w ∉ effs) →
    (∀ rt j, MemEff.storeb rt r j ∈ effs → j / 8 ≠ w) →
    (∀ rt j', MemEff.store32 rt r j' ∈ effs → j' + 4 ≤ 8 * w ∨ 8 * w + 8 ≤ j') →
    regionWord bytePA y r w = regionWord bytePA x r w) ∧
  (∀ r ∈ regions, ∀ j, j < 8 * r.words → (∀ rt, MemEff.storeb rt r j ∉ effs) →
    (∀ rt, MemEff.store rt r (j / 8) ∉ effs) →
    (∀ rt j', MemEff.store32 rt r j' ∈ effs → ¬ (j' ≤ j ∧ j < j' + 4)) →
    regionByte bytePA y r j = regionByte bytePA x r j)


end ArmCertValue.Physical
