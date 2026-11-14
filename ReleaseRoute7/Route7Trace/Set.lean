-- Route 7 CT0 (loops): memset's public trace schedule. The only data record is the STRB at tick 2 + 4i, writing d + i
-- (one byte); the fill value never enters a record. PCs follow the public offset schedule (base, returnPC, n).
import Route7Trace.Basic
import Route7Set.Context
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option Elab.async false
namespace Route7Set
open ArmCertLoop ArmCertLoop.SetNative ArmCertLoop.ContractDraft

def setRecs {domain : QueryDomain} (spec : TopologyImageSpec domain) (d : BitVec 64) (n : Nat) : Route7Trace.Recs :=
  fun k =>
    if 2 ≤ k ∧ (k - 2) % 4 = 0 ∧ (k - 2) / 4 < n then
      HeapV2StepCerts.DataRecs.dataRecs spec (d + BitVec.ofNat 64 ((k - 2) / 4)) true 1
    else []

abbrev recsOfS (c : Context) : Route7Trace.Recs := setRecs c.spec c.d c.n
abbrev pcOfS (c : Context) (k : Nat) : BitVec 64 := c.base + SetNative.offset c k

theorem recs_strb_s (c : Context) (i : Nat) (room : i < c.n) :
    (recsOfS c) (2 + 4 * i) = HeapV2StepCerts.DataRecs.dataRecs c.spec (c.d + BitVec.ofNat 64 i) true 1 := by
  have h : (2 + 4 * i - 2) / 4 = i := by omega
  simp only [recsOfS, setRecs]
  rw [if_pos ⟨by omega, by omega, by omega⟩, h]

theorem recs_nil_s (c : Context) (k : Nat) (h : ¬ (2 ≤ k ∧ (k - 2) % 4 = 0 ∧ (k - 2) / 4 < c.n)) : (recsOfS c) k = [] := by
  simp only [recsOfS, setRecs]
  rw [if_neg h]

theorem recs_pre_s (c : Context) (k : Nat) (hk : k < 2) : (recsOfS c) k = [] := recs_nil_s c k (by omega)

theorem recs_body_s (c : Context) (i j : Nat) (hj : 1 ≤ j) (hj4 : j < 4) : (recsOfS c) (2 + 4 * i + j) = [] :=
  recs_nil_s c _ (by omega)

theorem recs_exit_s (c : Context) : (recsOfS c) (2 + 4 * c.n) = [] := recs_nil_s c _ (by omega)

theorem pcAt_of_env_s (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k : Nat)
    (x : NativeState) (env : EnvS c catalogue entry k x) : x.regs._PC = pcOfS c k :=
  env.core.v1.pc

end Route7Set
#print axioms Route7Set.recs_strb_s
#print axioms Route7Set.recs_body_s
