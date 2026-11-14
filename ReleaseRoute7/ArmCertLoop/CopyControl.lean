import ArmCertLoop.CopyGeometry
import ArmCertLoop.ValueFacts
import LoopNative.NextABI
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions
open ArmCert.Translate ArmCert.Translate.Model ArmCertWalk
open ArmBridge.Draft ArmBridge.Boundary ArmBridge.CruxGenGuarded
open ArmBridge.CruxGenGuarded.ChainInv
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 1024
set_option Elab.async false
namespace ArmCertLoop.CopyNative
open ContractDraft

/-- The actual loop-back CBNZ uses the full64 counter. Its decision and next
PC are derived here from the current invariant, not supplied by a caller. -/
theorem branch_step (real : Type) [Sail.SailReal real] (c : Context) (i : Nat) (room : i < c.n)
    (x : NativeState) (env : Env c (2 + 6 * i + 5) x)
    (remaining : x.regs.gpr[2].toNat = c.n - (i + 1)) :
    ∃ y, modelStep real x = .ok () y ∧ Env c (2 + 6 * i + 6) y ∧ y.mem = x.mem ∧
      y.regs.gpr = x.regs.gpr ∧ y.regs.SP_EL0 = x.regs.SP_EL0 ∧ NativeEntry.Effects.Frame {} x.regs y.regs := by
  have fetch : FetchObligations c.spec c.config c.rows c.mapping
      (LoopNative.Cbnz64.Dispatch.selected 2#5 backImmediate) x := by
    exact fetch_index c (2 + 6 * i + 5) 7 x env (by decide) (by
      simpa only [Generated.imageStart, Generated.armcert_memcpy_entry] using
        pc_body c i 5 room (by decide) x env)
  by_cases again : i + 1 < c.n
  · have nonzero : x.regs.gpr[2] ≠ 0#64 := by
      intro same
      have zero := congrArg BitVec.toNat same
      simp only [BitVec.toNat_ofNat] at zero
      omega
    have condition : LoopNative.Cbnz64.condition 2#5 x := (LoopNative.Cbnz64.condition_iff 2#5 x).2 nonzero
    obtain ⟨y, run, nextInv, holds, memory, _, _, kept⟩ :=
      LoopNative.Cbnz64.next_taken_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
        c.base (offset c.base c.returnPC c.n) c.budget (2 + 6 * i + 5)
        (body_room c i 5 room (by decide)) c.page (body_aligned c i 5 room (by decide))
        2#5 backImmediate (by decide) x env condition (branch_low c i room x env)
        (branch_taken_placed c i again x env) fetch
    exact ⟨y, run, nextInv, memory, ValueFacts.nil_gpr x y holds, ValueFacts.nil_sp x y holds, kept⟩
  · have zero : x.regs.gpr[2] = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      change x.regs.gpr[2].toNat = 0
      omega
    have condition : ¬ LoopNative.Cbnz64.condition 2#5 x := by
      intro h
      exact ((LoopNative.Cbnz64.condition_iff 2#5 x).1 h) zero
    obtain ⟨y, run, nextInv, holds, memory, _, _, kept⟩ :=
      LoopNative.Cbnz64.next_not_taken_abi real c.spec c.config c.rows c.mapping c.consumer codeScope image c.base c.separated
        c.base (offset c.base c.returnPC c.n) c.budget (2 + 6 * i + 5)
        (body_room c i 5 room (by decide)) c.page (body_aligned c i 5 room (by decide))
        2#5 backImmediate (by decide) x env condition (branch_not_placed c i (by omega) room x env) fetch
    exact ⟨y, run, nextInv, memory, ValueFacts.nil_gpr x y holds, ValueFacts.nil_sp x y holds, kept⟩

#print axioms branch_step
end ArmCertLoop.CopyNative
