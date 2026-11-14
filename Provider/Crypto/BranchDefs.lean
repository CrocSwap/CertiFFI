-- BR8 lever L1 (next train): shared Bcond/Cbz defs split out of Crypto.BcondCore so the
-- Crypto/SDKPA/RtBr branch cores build in parallel. Definitions byte-identical, names unchanged.
import Bridge.CruxNonProj
import Crypto.BcondDecode
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
namespace Crypto.BcondCore
open Crypto.BcondDec

/-- The B.cond branch condition exactly as the flat native BR_BCondH.native states it. -/
def bcondC (cond : BitVec 4) (r : Regs) : Prop :=
  if Sail.BitVec.join1 [Sail.BitVec.access cond 0] = 1#1 ∧ ¬cond = 15#4 then
    if cond = 0#4 then ¬r.PSTATE.Z = 1#1 else if cond = 1#4 then ¬r.PSTATE.Z = 1#1
    else if cond = 2#4 then ¬r.PSTATE.C = 1#1 else if cond = 3#4 then ¬r.PSTATE.C = 1#1
    else if cond = 4#4 then ¬r.PSTATE.N = 1#1 else if cond = 5#4 then ¬r.PSTATE.N = 1#1
    else if cond = 6#4 then ¬r.PSTATE.V = 1#1 else if cond = 7#4 then ¬r.PSTATE.V = 1#1
    else if cond = 8#4 then (r.PSTATE.C = 1#1 → ¬r.PSTATE.Z = 0#1)
    else if cond = 9#4 then (r.PSTATE.C = 1#1 → ¬r.PSTATE.Z = 0#1)
    else if cond = 10#4 then ¬r.PSTATE.N = r.PSTATE.V else if cond = 11#4 then ¬r.PSTATE.N = r.PSTATE.V
    else if cond = 12#4 then (r.PSTATE.N = r.PSTATE.V → ¬r.PSTATE.Z = 0#1)
    else cond = 13#4 ∧ (r.PSTATE.N = r.PSTATE.V → ¬r.PSTATE.Z = 0#1)
  else
    if cond = 0#4 then r.PSTATE.Z = 1#1 else if cond = 1#4 then r.PSTATE.Z = 1#1
    else if cond = 2#4 then r.PSTATE.C = 1#1 else if cond = 3#4 then r.PSTATE.C = 1#1
    else if cond = 4#4 then r.PSTATE.N = 1#1 else if cond = 5#4 then r.PSTATE.N = 1#1
    else if cond = 6#4 then r.PSTATE.V = 1#1 else if cond = 7#4 then r.PSTATE.V = 1#1
    else if cond = 8#4 then (r.PSTATE.C = 1#1 ∧ r.PSTATE.Z = 0#1)
    else if cond = 9#4 then (r.PSTATE.C = 1#1 ∧ r.PSTATE.Z = 0#1)
    else if cond = 10#4 then r.PSTATE.N = r.PSTATE.V else if cond = 11#4 then r.PSTATE.N = r.PSTATE.V
    else if cond = 12#4 then (r.PSTATE.N = r.PSTATE.V ∧ r.PSTATE.Z = 0#1)
    else (¬cond = 13#4 ∨ (r.PSTATE.N = r.PSTATE.V ∧ r.PSTATE.Z = 0#1))

/-- Frame of a branch step on everything projectM reads besides the PC, plus mem/events. -/
structure BrFrame (S t : SequentialState Regs oracleChoiceSource) : Prop where
  mem : t.mem = S.mem
  events : t.events = S.events
  gpr : t.regs.gpr = S.regs.gpr
  sp : t.regs.SP_EL0 = S.regs.SP_EL0
  z : t.regs._Z = S.regs._Z
  pstate : t.regs.PSTATE = S.regs.PSTATE
  b64 : t.regs.bank_BitVec_64 = S.regs.bank_BitVec_64
  btn : t.regs.BTypeNext = S.regs.BTypeNext
  bbool : ∀ k, k ≠ Bank_Bool.SPESamplePreviousBranchAddressValid → t.regs.bank_Bool k = S.regs.bank_Bool k
  feat : t.regs.FeatureImpl = S.regs.FeatureImpl
  b32 : t.regs.bank_BitVec_32 = S.regs.bank_BitVec_32
  bint : t.regs.bank_Int = S.regs.bank_Int
  ss : t.regs.ShouldAdvanceSS = S.regs.ShouldAdvanceSS
  it : t.regs.ShouldAdvanceIT = S.regs.ShouldAdvanceIT
  enc : t.regs.__ThisInstrEnc = S.regs.__ThisInstrEnc
  emu : t.regs.__emulator_termination_opcode = S.regs.__emulator_termination_opcode
  b128 : t.regs.bank_BitVec_128 = S.regs.bank_BitVec_128
  sp1 : t.regs.SP_EL1 = S.regs.SP_EL1
  sp2 : t.regs.SP_EL2 = S.regs.SP_EL2
  sp3 : t.regs.SP_EL3 = S.regs.SP_EL3
  npe : ArmCertCT.CT2.NonProjRegsEq ArmBridge.CruxNonProj.bkHeap S.regs t.regs
  gic : t.regs.bank_Option_InterruptID .__GIC_Pending = S.regs.bank_Option_InterruptID .__GIC_Pending

end Crypto.BcondCore
