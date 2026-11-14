import CT1.Tables.Secp
set_option autoImplicit false

/-!
# CT1 secp: the DIT shim template and its G5 operand table

The 11 shim words of every secp card (DitShim243.Fetches.word), BL immediate per card:

| j (shim) | run step | word | instruction | register / state inputs | in DIT window? |
|---|---|---|---|---|---|
| 0 | 0 | 0xd503245f | BTI c | none | no |
| 1 | 1 | 0xd10043ff | SUB SP, SP, #16 | SP | no |
| 2 | 2 | 0xd53b42a9 | MRS X9, DIT | PSTATE.DIT (caller's) | no |
| 3 | 3 | 0xa9007be9 | STP X9, X30, [SP] | SP, X9, X30 | no |
| 4 | 4 | 0xd503415f | MSR DIT, #1 | none | no (sets DIT) |
| 5 | 5 | 0xd5033fdf | ISB | none | yes |
| 6 | 6 | BL body | BL | PC | yes |
| 7 | L+8 | 0xa9407be9 | LDP X9, X30, [SP] | SP, shim slot | yes |
| 8 | L+9 | 0x910043ff | ADD SP, SP, #16 | SP | yes |
| 9 | L+10 | 0xd51b42a9 | MSR DIT, X9 | X9 | state L+10 has DIT = 1; restores caller DIT |
| 10 | L+11 | 0xd65f03c0 | RET | X30 | no |

G5: every input above is SP (fixed by each run's entry check: pins.sp), X30 (the caller's
return address: equal across the pair by the GPR premise), the shim's own save slot, or X9 / PSTATE.DIT. X9 at L+10 is
the run's OWN caller-DIT image (MRS at step 2, saved at step 3, slot unchanged across W, reloaded at L+8:
DitShim243.Factory / EpiFactory). PSTATE.DIT is not in the declared secret set (memory, and x1 on cmul), so no
out-of-window operand is secret-dependent. No cross-run equality of the entry DIT is claimed.
-/

namespace CT1.SecpShim
open CT1.Words

/-- The shim words in shim order, with the card's BL word. -/
def template (bl : Nat) : List Nat :=
  [0xd503245f, 0xd10043ff, 0xd53b42a9, 0xa9007be9, 0xd503415f, 0xd5033fdf, bl,
   0xa9407be9, 0x910043ff, 0xd51b42a9, 0xd65f03c0]

/-- The template's non-BL words are reviewed table rows with these classes. -/
theorem template_classes :
    ([0xd503245f, 0xd10043ff, 0xd53b42a9, 0xa9007be9, 0xd503415f, 0xd5033fdf,
      0xa9407be9, 0x910043ff, 0xd51b42a9, 0xd65f03c0].map (fun w => CT1.Tables.Secp.table.lookup w)) =
    ([some .shimControl, some .immediateArithmetic, some .shimControl, some .storePair, some .shimControl,
     some .shimControl, some .loadPair, some .immediateArithmetic, some .shimControl, some .publicReturn] : List (Option Cls)) := by
  decide

set_option maxRecDepth 100000 in
/-- K4 mutant: MOVK (opc = 11, reads its destination) is not a window word; MOVZ (opc = 10) is `noDataInput`. -/
theorem mutant_movk : windowListed CT1.Tables.Secp.table [0xf2800020] = false := by decide +kernel

end CT1.SecpShim
