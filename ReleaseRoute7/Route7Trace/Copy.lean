-- Route 7 CT0 (loops): memcpy's public trace schedule. The data records depend only on (d, s, n): LDRB at tick 2 + 6i
-- reads s + i, STRB at tick 3 + 6i writes d + i (one byte each); every other tick has no data record. PCs follow the
-- public offset schedule (base, returnPC, n).
import Route7Trace.Basic
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option Elab.async false
namespace Route7Copy
open ArmCertLoop ArmCertLoop.CopyNative ArmCertLoop.ContractDraft

def copyRecs {domain : QueryDomain} (spec : TopologyImageSpec domain) (d s : BitVec 64) (n : Nat) : Route7Trace.Recs :=
  fun k =>
    if 2 ≤ k ∧ (k - 2) % 6 = 0 ∧ (k - 2) / 6 < n then
      HeapV2StepCerts.DataRecs.dataRecs spec (s + BitVec.ofNat 64 ((k - 2) / 6)) false 1
    else if 3 ≤ k ∧ (k - 3) % 6 = 0 ∧ (k - 3) / 6 < n then
      HeapV2StepCerts.DataRecs.dataRecs spec (d + BitVec.ofNat 64 ((k - 3) / 6)) true 1
    else []

abbrev recsOf (c : Context) : Route7Trace.Recs := copyRecs c.spec c.d c.s c.n
abbrev pcOf (c : Context) (k : Nat) : BitVec 64 := c.base + offset c.base c.returnPC c.n k

theorem recs_ldrb (c : Context) (i : Nat) (room : i < c.n) :
    (recsOf c) (2 + 6 * i) = HeapV2StepCerts.DataRecs.dataRecs c.spec (c.s + BitVec.ofNat 64 i) false 1 := by
  have h : (2 + 6 * i - 2) / 6 = i := by omega
  simp only [recsOf, copyRecs]
  rw [if_pos ⟨by omega, by omega, by omega⟩, h]

theorem recs_strb (c : Context) (i : Nat) (room : i < c.n) :
    (recsOf c) (2 + 6 * i + 1) = HeapV2StepCerts.DataRecs.dataRecs c.spec (c.d + BitVec.ofNat 64 i) true 1 := by
  have h : (2 + 6 * i + 1 - 3) / 6 = i := by omega
  simp only [recsOf, copyRecs]
  rw [if_neg (by omega), if_pos ⟨by omega, by omega, by omega⟩, h]

theorem recs_nil (c : Context) (k : Nat) (h1 : ¬ (2 ≤ k ∧ (k - 2) % 6 = 0 ∧ (k - 2) / 6 < c.n))
    (h2 : ¬ (3 ≤ k ∧ (k - 3) % 6 = 0 ∧ (k - 3) / 6 < c.n)) : (recsOf c) k = [] := by
  simp only [recsOf, copyRecs]
  rw [if_neg h1, if_neg h2]

theorem recs_pre (c : Context) (k : Nat) (hk : k < 2) : (recsOf c) k = [] :=
  recs_nil c k (by omega) (by omega)

theorem recs_body (c : Context) (i j : Nat) (room : i < c.n) (hj : 2 ≤ j) (hj6 : j < 6) : (recsOf c) (2 + 6 * i + j) = [] :=
  recs_nil c _ (by omega) (by omega)

theorem recs_exit (c : Context) : (recsOf c) (2 + 6 * c.n) = [] :=
  recs_nil c _ (by omega) (by omega)

theorem pcAt_of_env (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k : Nat)
    (x : NativeState) (env : EnvR c catalogue entry k x) : x.regs._PC = (pcOf c) k :=
  env.core.v1.pc

end Route7Copy
#print axioms Route7Copy.recs_ldrb
#print axioms Route7Copy.recs_strb
#print axioms Route7Copy.recs_body
