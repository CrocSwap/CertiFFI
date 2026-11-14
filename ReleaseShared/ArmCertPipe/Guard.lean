-- d199 pipeline P1: a case's path conditions as data over the value table. Each conditional branch on the
-- case's path contributes one Guard over the table ids its operands have at that step (P1 computes them from
-- compileRun on the plan prefix and kernel-checks them). The math lemmas take PathOK as a premise; the branch routes and
-- the E17 chain read the same guards through Agrees, so one predicate serves both.
import ArmCertValue.Run
set_option autoImplicit false
namespace ArmCertPipe
open ArmCertValue

inductive Guard where
  /-- B.cond: ConditionHolds c on the flag words (ids n z cf v) is `b`. -/
  | cond (c : BitVec 4) (n z cf v : Nat) (b : Bool)
  /-- CBZ/CBNZ: the register value (low 32 bits if `w32`) is zero iff `b`. -/
  | zero (id : Nat) (w32 : Bool) (b : Bool)
  /-- TBZ/TBNZ: bit `i` of the register value is `b`. -/
  | bit (id i : Nat) (b : Bool)
  deriving DecidableEq, Repr

def Guard.holds (vals : List (BitVec 64)) : Guard → Prop
  | .cond c n z cf v b => condHolds c (vals.getD n 0) (vals.getD z 0) (vals.getD cf 0) (vals.getD v 0) = b
  | .zero i w32 b => decide ((if w32 then (vals.getD i 0).setWidth 32 = 0 else vals.getD i 0 = 0)) = b
  | .bit i j b => (vals.getD i 0).getLsbD j = b

/-- The case's path is taken: every guard holds on the table values. -/
def PathOK (vals : List (BitVec 64)) (gs : List Guard) : Prop := ∀ g ∈ gs, g.holds vals

/-- The ids a guard reads at the branch step, as a function of the symbolic state there (for the kernel check). -/
def Guard.ids? (σ : Sym) (r : HeapV2StepCerts.RegBind.Reg) : Guard → Option Guard
  | .cond c _ _ _ _ b => σ.nzcv.map fun (n, z, cf, v) => .cond c n z cf v b
  | .zero _ w32 b => (σ.regs r).map fun i => .zero i w32 b
  | .bit _ j b => (σ.regs r).map fun i => .bit i j b

end ArmCertPipe
