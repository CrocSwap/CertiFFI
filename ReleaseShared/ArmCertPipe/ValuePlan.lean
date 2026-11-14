import ArmCertPipe.FPrefix
import ArmCertPipe.GPrefix

set_option autoImplicit false

namespace ArmCertPipe.ValuePlan
open ArmCertValue HeapV2StepCerts.RegBind

inductive Language where
  | f
  | g
  deriving DecidableEq

def Step : Language → Type
  | .f => ArmCertValue.F.Step
  | .g => ArmCertValue.G.Step

def compileRun (language : Language) (regions : List Region) (initial : Sym) (next : Nat)
    (plan : List (Step language)) : Option (List Def × Sym) :=
  match language with
  | .f => ArmCertValue.F.compileRun regions initial next plan
  | .g => ArmCertValue.G.compileRun regions initial next plan

def Holds (language : Language) (view : Physical.BytePA) (regions : List Region)
    (step : Step language) (x y : St) : Prop :=
  match language with
  | .f => ArmCertValue.F.Holds view regions step x y
  | .g => ArmCertValue.G.Holds view regions step x y

def AgreesAt (language : Language) (view : Physical.BytePA) (regions : List Region)
    (initial : Sym) (inputs : List (BitVec 64)) (plan : List (Step language))
    (k : Nat) (x : St) : Prop :=
  ∃ defs result, compileRun language regions initial inputs.length (plan.take k) = some (defs,result) ∧
    Physical.Agrees view (extend inputs defs) result x ∧ result.Bounded (extend inputs defs).length

def legacy (language : Language) (step : StepV) : Step language :=
  match language with
  | .f => .legacy step
  | .g => ArmCertValue.G.Step.legacy (.legacy step)

theorem holds_legacy (language : Language) (view : Physical.BytePA) (regions : List Region)
    (step : StepV) (x y : St) :
    Holds language view regions (legacy language step) x y ↔
      ArmCertValue.F.Holds view regions (.legacy step) x y := by
  cases language <;> rfl

theorem initial (language : Language) (view : Physical.BytePA) (regions : List Region)
    (initial : Sym) (inputs : List (BitVec 64)) (plan : List (Step language)) (x : St)
    (agreement : Physical.Agrees view inputs initial x) (bounded : initial.Bounded inputs.length) :
    AgreesAt language view regions initial inputs plan 0 x := by
  cases language with
  | f => exact ArmCertPipe.F.agreesAt_zero (regions := regions) (plan := plan) agreement bounded
  | g => exact ArmCertPipe.G.agreesAt_zero (regions := regions) (plan := plan) agreement bounded

theorem advance (language : Language) (view : Physical.BytePA) (regions : List Region)
    (initial : Sym) (inputs : List (BitVec 64)) (plan : List (Step language))
    (k : Nat) (x y : St) (room : k < plan.length)
    (compiled : (compileRun language regions initial inputs.length plan).isSome = true)
    (agreement : AgreesAt language view regions initial inputs plan k x)
    (effect : Holds language view regions plan[k] x y) :
    AgreesAt language view regions initial inputs plan (k + 1) y := by
  cases language with
  | f => exact ArmCertPipe.F.agreesAt_succ room compiled agreement effect
  | g => exact ArmCertPipe.G.agreesAt_succ room compiled agreement effect

theorem register_value (language : Language) (view : Physical.BytePA) (regions : List Region)
    (initial : Sym) (inputs : List (BitVec 64)) (plan : List (Step language))
    (k : Nat) (x : St) (defs : List Def) (result : Sym)
    (agreement : AgreesAt language view regions initial inputs plan k x)
    (compiled : compileRun language regions initial inputs.length plan = some (defs,result))
    (r : Reg) (index : Nat)
    (current : (compileRun language regions initial inputs.length (plan.take k)).map
      (fun p => p.2.regs r) = some (some index)) :
    regVal x r = (extend inputs defs).getD index 0 := by
  cases language with
  | f => exact ArmCertPipe.F.regVal_of_agreesAt agreement compiled current
  | g => exact ArmCertPipe.G.regVal_of_agreesAt agreement compiled current

#print axioms holds_legacy
#print axioms initial
#print axioms advance
#print axioms register_value
end ArmCertPipe.ValuePlan
