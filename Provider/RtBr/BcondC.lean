-- RtBr.BcondC: Sail-level B.cond condition (copy of the Sail if-condition of BR_BCondH.native).
import BR8.BCond
import SDKPA.BranchPins
import SDKPA.BranchPinsF
import Crypto.BrSimp
import Pilot.ObservationSimp
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register EvalProfile
set_option autoImplicit false
namespace RtBr.BcondC

def bcondC (cond : BitVec 4) (r : ArmFull.Regs) : Prop :=
  if Sail.BitVec.join1 [Sail.BitVec.access cond 0] = 1#1 ∧ ¬cond = 15#4 then
    if cond = 0#4 then ¬r.PSTATE.Z = 1#1
    else
      if cond = 1#4 then ¬r.PSTATE.Z = 1#1
      else
        if cond = 2#4 then ¬r.PSTATE.C = 1#1
        else
          if cond = 3#4 then ¬r.PSTATE.C = 1#1
          else
            if cond = 4#4 then ¬r.PSTATE.N = 1#1
            else
              if cond = 5#4 then ¬r.PSTATE.N = 1#1
              else
                if cond = 6#4 then ¬r.PSTATE.V = 1#1
                else
                  if cond = 7#4 then ¬r.PSTATE.V = 1#1
                  else
                    if cond = 8#4 then r.PSTATE.C = 1#1 → ¬r.PSTATE.Z = 0#1
                    else
                      if cond = 9#4 then r.PSTATE.C = 1#1 → ¬r.PSTATE.Z = 0#1
                      else
                        if cond = 10#4 then ¬r.PSTATE.N = r.PSTATE.V
                        else
                          if cond = 11#4 then ¬r.PSTATE.N = r.PSTATE.V
                          else
                            if cond = 12#4 then r.PSTATE.N = r.PSTATE.V → ¬r.PSTATE.Z = 0#1
                            else cond = 13#4 ∧ (r.PSTATE.N = r.PSTATE.V → ¬r.PSTATE.Z = 0#1)
  else
    if cond = 0#4 then r.PSTATE.Z = 1#1
    else
      if cond = 1#4 then r.PSTATE.Z = 1#1
      else
        if cond = 2#4 then r.PSTATE.C = 1#1
        else
          if cond = 3#4 then r.PSTATE.C = 1#1
          else
            if cond = 4#4 then r.PSTATE.N = 1#1
            else
              if cond = 5#4 then r.PSTATE.N = 1#1
              else
                if cond = 6#4 then r.PSTATE.V = 1#1
                else
                  if cond = 7#4 then r.PSTATE.V = 1#1
                  else
                    if cond = 8#4 then r.PSTATE.C = 1#1 ∧ r.PSTATE.Z = 0#1
                    else
                      if cond = 9#4 then r.PSTATE.C = 1#1 ∧ r.PSTATE.Z = 0#1
                      else
                        if cond = 10#4 then r.PSTATE.N = r.PSTATE.V
                        else
                          if cond = 11#4 then r.PSTATE.N = r.PSTATE.V
                          else
                            if cond = 12#4 then r.PSTATE.N = r.PSTATE.V ∧ r.PSTATE.Z = 0#1
                            else ¬cond = 13#4 ∨ r.PSTATE.N = r.PSTATE.V ∧ r.PSTATE.Z = 0#1

end RtBr.BcondC
