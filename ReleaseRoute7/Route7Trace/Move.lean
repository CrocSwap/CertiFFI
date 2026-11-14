-- Route 7 CT0 (loops): memmove's public trace schedule, by public path (movePath d s n). Forward: LDRB s+i at tick
-- 5+6i, STRB d+i at 6+6i. Backward: LDRB s+(n-1-t) at 8+6t, STRB d+(n-1-t) at 9+6t. Empty / same paths and every
-- other tick: no data record. PCs follow the public offset schedule.
import Route7Trace.Basic
import Route7Move.Context
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
set_option autoImplicit false
set_option Elab.async false
namespace Route7Move
open ArmCertLoop ArmCertLoop.ContractDraft

def moveRecs {domain : QueryDomain} (spec : TopologyImageSpec domain) (d s : BitVec 64) (n : Nat) :
    Schedule.MovePath → Route7Trace.Recs
  | .forward => fun k =>
    if 5 ≤ k ∧ (k - 5) % 6 = 0 ∧ (k - 5) / 6 < n then
      HeapV2StepCerts.DataRecs.dataRecs spec (s + BitVec.ofNat 64 ((k - 5) / 6)) false 1
    else if 6 ≤ k ∧ (k - 6) % 6 = 0 ∧ (k - 6) / 6 < n then
      HeapV2StepCerts.DataRecs.dataRecs spec (d + BitVec.ofNat 64 ((k - 6) / 6)) true 1
    else []
  | .backward => fun k =>
    if 8 ≤ k ∧ (k - 8) % 6 = 0 ∧ (k - 8) / 6 < n then
      HeapV2StepCerts.DataRecs.dataRecs spec (s + BitVec.ofNat 64 (n - 1 - (k - 8) / 6)) false 1
    else if 9 ≤ k ∧ (k - 9) % 6 = 0 ∧ (k - 9) / 6 < n then
      HeapV2StepCerts.DataRecs.dataRecs spec (d + BitVec.ofNat 64 (n - 1 - (k - 9) / 6)) true 1
    else []
  | _ => fun _ => []

abbrev recsOfM (c : Context) : Route7Trace.Recs := moveRecs c.spec c.d c.s c.n c.path
abbrev pcOfM (c : Context) (k : Nat) : BitVec 64 := c.base + Route7Move.offset c k

section
variable (c : Context)

theorem recs_fwd_ldrb (fwd : c.path = .forward) (i : Nat) (room : i < c.n) :
    (recsOfM c) (5 + 6 * i) = HeapV2StepCerts.DataRecs.dataRecs c.spec (c.s + BitVec.ofNat 64 i) false 1 := by
  have h : (5 + 6 * i - 5) / 6 = i := by omega
  simp only [recsOfM, fwd, moveRecs]
  rw [if_pos ⟨by omega, by omega, by omega⟩, h]

theorem recs_fwd_strb (fwd : c.path = .forward) (i : Nat) (room : i < c.n) :
    (recsOfM c) (5 + 6 * i + 1) = HeapV2StepCerts.DataRecs.dataRecs c.spec (c.d + BitVec.ofNat 64 i) true 1 := by
  have h : (5 + 6 * i + 1 - 6) / 6 = i := by omega
  simp only [recsOfM, fwd, moveRecs]
  rw [if_neg (by omega), if_pos ⟨by omega, by omega, by omega⟩, h]

theorem recs_fwd_nil (fwd : c.path = .forward) (k : Nat) (h1 : ¬ (5 ≤ k ∧ (k - 5) % 6 = 0 ∧ (k - 5) / 6 < c.n))
    (h2 : ¬ (6 ≤ k ∧ (k - 6) % 6 = 0 ∧ (k - 6) / 6 < c.n)) : (recsOfM c) k = [] := by
  simp only [recsOfM, fwd, moveRecs]
  rw [if_neg h1, if_neg h2]

theorem recs_bwd_ldrb (bwd : c.path = .backward) (t : Nat) (room : t < c.n) :
    (recsOfM c) (6 + 6 * t + 2) =
      HeapV2StepCerts.DataRecs.dataRecs c.spec (c.s + BitVec.ofNat 64 (c.n - 1 - t)) false 1 := by
  have h : (6 + 6 * t + 2 - 8) / 6 = t := by omega
  simp only [recsOfM, bwd, moveRecs]
  rw [if_pos ⟨by omega, by omega, by omega⟩, h]

theorem recs_bwd_strb (bwd : c.path = .backward) (t : Nat) (room : t < c.n) :
    (recsOfM c) (6 + 6 * t + 3) =
      HeapV2StepCerts.DataRecs.dataRecs c.spec (c.d + BitVec.ofNat 64 (c.n - 1 - t)) true 1 := by
  have h : (6 + 6 * t + 3 - 9) / 6 = t := by omega
  simp only [recsOfM, bwd, moveRecs]
  rw [if_neg (by omega), if_pos ⟨by omega, by omega, by omega⟩, h]

theorem recs_bwd_nil (bwd : c.path = .backward) (k : Nat) (h1 : ¬ (8 ≤ k ∧ (k - 8) % 6 = 0 ∧ (k - 8) / 6 < c.n))
    (h2 : ¬ (9 ≤ k ∧ (k - 9) % 6 = 0 ∧ (k - 9) / 6 < c.n)) : (recsOfM c) k = [] := by
  simp only [recsOfM, bwd, moveRecs]
  rw [if_neg h1, if_neg h2]

theorem recs_empty (p : c.path = .empty) (k : Nat) : (recsOfM c) k = [] := by
  simp only [recsOfM, p, moveRecs]

theorem recs_same (p : c.path = .same) (k : Nat) : (recsOfM c) k = [] := by
  simp only [recsOfM, p, moveRecs]
end

theorem pcAt_of_env_m (c : Context) (catalogue : NativeMteTagCheck.ControlCatalogue) (entry : NativeState) (k : Nat)
    (x : NativeState) (env : EnvM c catalogue entry k x) : x.regs._PC = pcOfM c k :=
  env.core.v1.pc

end Route7Move
#print axioms Route7Move.recs_fwd_ldrb
#print axioms Route7Move.recs_bwd_strb
#print axioms Route7Move.recs_same
