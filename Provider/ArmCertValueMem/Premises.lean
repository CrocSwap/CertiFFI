-- Memory: the heap-v2 region map and the two deployment premises of the memory value steps memV_k.
-- ArmCert-only (ArmCertValue.Core + HeapV2 plan / pin tables).
import HeapV2StepCerts.RegBindCore
import ArmCertValue.Core
import ArmCertValue.HeapV2Plan
import ArmCertTranslateModel.HeapV2E17Table
import ArmCertTranslateModel.HeapV2Plan
set_option autoImplicit false
namespace ArmCertValue.HeapV2Mem
open ArmCertValue ArmCert.Translate.Model

/-- The region map is certiffi's ArmCertValue.HeapV2Plan.{I, O, F, regions} (generated plan's constants, reused so the
plan's MemEffs and memV_k agree syntactically): I = ⟨2,0,4⟩ (x1+[0,32)), O = ⟨1,0,4⟩ (x0+[0,32)), F = ⟨0,-64,8⟩ ([sp-64,sp)). -/
abbrev I : Region := ArmCertValue.HeapV2Plan.I
abbrev O : Region := ArmCertValue.HeapV2Plan.O
abbrev F : Region := ArmCertValue.HeapV2Plan.F
abbrev regions : List Region := ArmCertValue.HeapV2Plan.regions

/-- The pin valuation of the regions: Region.pin 0 / 1 / 2 = pins.sp / x0 / x1 (HeapV2E17.pin). -/
abbrev pinv (p : HeapV2E17.Pins) : Nat → Nat := HeapV2E17.pin p

/-- The VA of byte j of region r: exactly the address regionByte reads. -/
def byteVA (p : HeapV2E17.Pins) (r : Region) (j : Nat) : BitVec 64 :=
  BitVec.ofInt 64 ((pinv p r.pin : Int) + r.off + j)

theorem regionByte_va (mapping : BitVec 64 → Option Nat) (p : HeapV2E17.Pins) (s : HeapV2StepCerts.RegBind.St)
    (r : Region) (j : Nat) :
    regionByte mapping (pinv p) s r j = (mapping (byteVA p r j)).bind fun pa => s.mem[pa]? := rfl

/-- All tracked bytes: (region, byte index), 32 + 32 + 64 = 128 of them. -/
def heapv2Bytes : List (Region × Nat) :=
  regions.flatMap fun r => (List.range (8 * r.words)).map fun j => (r, j)

/-- DEPLOYMENT PREMISE (decided on a concrete deployment): every plan access maps its bytes linearly,
mapping (dataVA + i) = mapping dataVA + i for i < size. A 16-byte access never crosses a page (16-aligned). -/
def DataBytesLinear (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) : Prop :=
  HeapV2Plan.symbolicAccesses.all (fun e => (List.range e.2.2.2.1).all fun i =>
    mapping (BitVec.ofInt 64 ((HeapV2E17.pin p e.2.1 : Int) + e.2.2.1 + i)) == (mapping (HeapV2E17.dataVA p e)).map (· + i)) = true

/-- CLAIM PRECONDITION: distinct tracked bytes of O, I and F never share a physical byte.
Split: (i) caller/pins: VA ranges [x0, x0+32), [x1, x1+32), [sp-64, sp) pairwise disjoint; (ii) the mapping
injective on those pages (, from the page rows; double mmap excluded as a deployment premise). -/
def RegionsInjective (p : HeapV2E17.Pins) (mapping : BitVec 64 → Option Nat) : Prop :=
  ∀ a, a ∈ heapv2Bytes → ∀ b, b ∈ heapv2Bytes → a ≠ b → ∀ n,
    mapping (byteVA p a.1 a.2) = some n → mapping (byteVA p b.1 b.2) ≠ some n

set_option maxRecDepth 8192 in
theorem heapv2Bytes_length : heapv2Bytes.length = 128 := by decide +kernel

end ArmCertValue.HeapV2Mem
