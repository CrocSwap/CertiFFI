set_option autoImplicit false

/-!
# CT1 (b)/(c): the generic DIT word vocabulary and the decided window / no-SVE checks

The class vocabulary is CertiFFI ArmDIT202509 (Arm A64 ISA2025-09_rel, DDI0602 ID092025, DIT Operational-information
clause), as used by F23.2 SecpDitWords, plus the -accepted additions of 18:11Z
(STRB/LDRB/LDR/STR/LDRH/STRH forms; independent footer attribution, 1027 DIT sections). A consumer's table is
generated per function by `tools/ct1/gen_dit_table.py` (encoding-field classifier + objdump + Sail `__DecodeA64` leaf,
all three must agree) and pinned by its sha.

Class meanings:
- A DIT class means the section carries Arm's DIT clause and the word is inside the classifier's encoding-field
  restriction (widths / addressing modes the proofs cover). DIT gives data-VALUE timing only. For loads and stores
  the address (base, offset, register offset) is an address input whose publicness comes from CT0, not from DIT.
- Public control (K4): B / BL / RET / B.cond / CBZ / CBNZ / TBZ / TBNZ. Not DIT-listed. Their conditions and targets
  are public because CT0 proves the PC sequence equal across the pair.
- `noDataInput` (MOVZ, 64-bit, opc = 10 only): not DIT-listed and not covered by P3; it has no register or flag input
 (only its immediate), so it has no data operand. Allowed in a window as a public constant (K4 refinement,
  ACCEPTED 18:38Z). MOVK (opc = 11) reads its destination and is NOT in this class.
- `shimControl` (BTI / ISB / MSR / MRS): never allowed inside a window; outside the window it is handled by G5.

Recognition is metadata: P3 (Arm's DIT timing contract) stays a CLAIM_CONDITION and is not a Lean axiom.
-/

namespace CT1.Words

inductive Cls where
  -- DIT-listed (ArmDIT202509 + reviewed additions)
  | andImmediate
  | carry
  | extract
  | immediateArithmetic
  | incrementSelect
  | invertSelect
  | loadPair
  | logicalShifted
  | multiplyAdd
  | negateSelect
  | orImmediate
  | select
  | shiftedArithmetic
  | storePair
  | unsignedBitfield
  | unsignedMultiplyAddLong
  | unsignedMultiplyHigh
  | loadByteImmediate
  | storeByteImmediate
  -- not DIT-listed
  | noDataInput
  | publicDirectCall
  | publicReturn
  | publicBranch
  | publicCondBranch
  | publicCompareBranch
  | shimControl
  deriving DecidableEq, Repr

/-- The section carries Arm's DIT clause (and the word is inside the reviewed encoding restriction). -/
def Cls.isDit : Cls → Bool
  | .andImmediate | .carry | .extract | .immediateArithmetic | .incrementSelect | .invertSelect | .loadPair
  | .logicalShifted | .multiplyAdd | .negateSelect | .orImmediate | .select | .shiftedArithmetic | .storePair
  | .unsignedBitfield | .unsignedMultiplyAddLong | .unsignedMultiplyHigh | .loadByteImmediate
  | .storeByteImmediate => true
  | _ => false

/-- K4 public control: B / BL / RET / B.cond / CBZ / CBNZ (TBZ / TBNZ when a consumer needs them). -/
def Cls.isPublicControl : Cls → Bool
  | .publicDirectCall | .publicReturn | .publicBranch | .publicCondBranch | .publicCompareBranch => true
  | _ => false

/-- Allowed inside a DIT window: DIT-listed, public control, or a no-data-input constant. -/
def Cls.windowOk (c : Cls) : Bool := c.isDit || c.isPublicControl || c == .noDataInput

/-- (b) Every word of the window is a table row whose class is allowed in a window. -/
def windowListed (table : List (Nat × Cls)) (ws : List Nat) : Bool :=
  ws.all fun w => match table.lookup w with
    | some c => c.windowOk
    | none => false

/-- coverage discipline (as CT2 S5): every word of a code list is either a window-listed table row or one of the
    G5-listed shim words. No word falls through both checks. -/
def windowOrShim (table : List (Nat × Cls)) (shim : List Nat) (ws : List Nat) : Bool :=
  ws.all fun w => (match table.lookup w with
    | some c => c.windowOk
    | none => false) || shim.contains w

/-- The A64 top-level op1 field, bits[28:25]. -/
def op1 (w : BitVec 32) : BitVec 4 := w.extractLsb' 25 4

/-- SVE (op1 = 0010) or SME (op0 = 1, op1 = 0000) encoding group (Arm A64 top-level encoding table). -/
def isSveSme (w : BitVec 32) : Bool :=
  op1 w == 0b0010#4 || (w.getLsbD 31 && op1 w == 0b0000#4)

/-- SMSTART / SMSTOP (MSR SVCRSM/SVCRZA/SVCRSMZA, #imm: op1 = 011, CRn = 0100, CRm = 0b0xxx, op2 = 011) and
 MSR SVCR, Xt (S3_3_C4_C2_2, 0xd51b424_). These are in the System group, not the SME op1 space. -/
def isSmControl (w : BitVec 32) : Bool :=
  (w &&& 0xfffff8ff#32) == 0xd503407f#32 || (w &&& 0xffffffe0#32) == 0xd51b4240#32

/-- (c) No word is SVE/SME, and no word is an SMSTART/SMSTOP/MSR SVCR form. -/
def noSveSme (ws : List Nat) : Bool :=
  ws.all fun w => !isSveSme (BitVec.ofNat 32 w) && !isSmControl (BitVec.ofNat 32 w)

theorem sve_example : isSveSme 0x04a00000#32 = true := by decide
theorem smstart_example : isSmControl 0xd503477f#32 = true := by decide
theorem smstop_example : isSmControl 0xd503467f#32 = true := by decide
theorem msr_svcr_example : isSmControl 0xd51b4249#32 = true := by decide
theorem msr_dit_not_sm : isSmControl 0xd503415f#32 = false := by decide
theorem ret_ok : isSveSme 0xd65f03c0#32 = false ∧ isSmControl 0xd65f03c0#32 = false := by decide

end CT1.Words
