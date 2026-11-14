-- load presence from physical prefix agreement, without mapping interior byte VAs.
import ArmCertMemPipe.FactsG
import ArmCertPipe.PhysicalPrefix
import ArmCertValue.PhysicalMemory
set_option autoImplicit false
namespace ArmCertMemPipe.PhysicalFactsG
open ArmCertValue ArmBridge.Draft
open ArmCertValue.Physical (BytePA Agrees)

theorem bytes_of_agrees {bytePA : BytePA} {vals : List (BitVec 64)} {σ : Sym} {x : NativeState}
    (h : Agrees bytePA vals σ x) (r : Region) (j0 n pa : Nat)
    (span : ∀ t : Nat, t < n → bytePA r (j0 + t) = some (pa + t))
    (cov : ∀ t : Nat, t < n → ∃ i k, σ.memB r (j0 + t) = some (i, k)) :
    ∃ v : BitVec (8 * n), ∀ t < n, x.mem[pa + t]? = some (v.extractLsb' (8 * t) 8) :=
  HeapV2StepCerts.C3.exists_value (fun t => x.mem[pa + t]?) n
    (ArmCertValue.Physical.bytes_present_of_agrees h r j0 n pa span cov)

theorem bytes_of_agreesAt {bytePA : BytePA} {regions : List Region} {σ0 : Sym}
    {inputs : List (BitVec 64)} {plan : List StepV} {k : Nat} {x : NativeState}
    (h : ArmCertPipe.Physical.AgreesAt bytePA regions σ0 inputs plan k x) (r : Region) (j0 n pa : Nat)
    (span : ∀ t : Nat, t < n → bytePA r (j0 + t) = some (pa + t))
    (cov : ∀ ds σ, compileRun regions σ0 inputs.length (plan.take k) = some (ds, σ) →
      ∀ t : Nat, t < n → ∃ i k', σ.memB r (j0 + t) = some (i, k')) :
    ∃ v : BitVec (8 * n), ∀ t < n, x.mem[pa + t]? = some (v.extractLsb' (8 * t) 8) := by
  obtain ⟨ds, σ, hc, ha, _⟩ := h
  exact bytes_of_agrees ha r j0 n pa span (cov ds σ hc)

#print axioms bytes_of_agreesAt
end ArmCertMemPipe.PhysicalFactsG
