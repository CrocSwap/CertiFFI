import BridgeDraft.StateProjection
import ArmFull.Fn.M1475

/-! Bridge.Boundary, Sail-only part (a design decision (c), d194): the frozen-model per-instruction epilogue
formStep and the SysregMove word class. Premises / FetchOK (stated over LNSym Program / project) moved to the
QUARANTINED module Bridge.BoundaryLNSym. -/
open Sail Sail.ConcurrencyInterfaceV1 ArmFull ArmFull.Functions ArmFull.Register
namespace ArmBridge.Boundary
open ArmBridge.Draft

/-- The frozen model per-instruction epilogue (ArmFull.Functions.__InstructionExecute)
around one form action, for non-ERET AArch64 forms: clear __BranchTaken, run the action
(the published decode root on the word fields), BTYPE := BTypeNext, PC += 4 unless taken.
ThisInstrLength is 32 for A64, so the model's addInt(pc, 32/8) is pc + 4. -/
def formStep (action : SailM Unit) : SailM Unit := do
  writeReg __BranchTaken false
  action
  let ps ← readReg PSTATE
  let next ← readReg BTypeNext
  writeReg PSTATE { ps with BTYPE := next }
  let taken ← readReg __BranchTaken
  if !taken then
    let pc ← readReg _PC
    writeReg _PC (pc + 4#64)

/-- MSR/MRS (register) encodings. Excluded program-wide, conservatively, so no instruction
can feed PMU/SPE/debug/trace bookkeeping back into projected state. -/
def SysregMove (w : BitVec 32) : Prop := (w &&& 0xFFD00000#32) = 0xD5100000#32

end ArmBridge.Boundary
