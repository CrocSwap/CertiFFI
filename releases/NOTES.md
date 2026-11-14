# Notes on the previous signed releases (Heap v1.1, Runtime14 v1.2; superseded)

These notes explain terms used in the previous signed claims, which are now superseded (see [CHANGELOG](CHANGELOG.md)). The current claims (Heap v1.3, Runtime14 v1.4) state both points in their own text. The notes do not amend any signed claim.

## What "constant-time" means in Heap v1.1 and Runtime14 v1.2

The claims refer to "constant-time (CT) variants" and their boundary theorems. In both releases, the CT theorems prove one thing: two executions on the same reviewed path, whose public inputs (buffer addresses and lengths) agree, produce the same **model event trace**. That trace is the model's ordered event record. It covers instruction fetch and the PC sequence, memory and translation-table-walk traffic, and barrier events. So the theorems establish identical control flow and identical memory and table-walk access patterns. The record has no data-operand timing component.

Concluding that hardware execution time is independent of secret operands needs one more fact: data-processing instructions must take operand-independent time. Arm guarantees this only for instructions on its Data Independent Timing (DIT) list, and only while `PSTATE.DIT = 1`. The Sail model does not contain that guarantee, and it is not measured; it is an external condition on the claim.

- **Heap v1.1.** The certified entry shim enables DIT before the body and restores the caller's value on exit.
  - A theorem in the released sources (`dit_window`, module `DefaultHeapShimDitWindow`) proves, under its stated hypotheses (the shim's entry conditions), that `PSTATE.DIT = 1` on every step from shim step 5 through step 367, which covers the whole body. It also proves that DIT equals its entry value at exit.
  - The signed headline exposes the epilogue part (`ditOn`, steps 365–367) and the restoration (`ditRestored`).
  - With Arm's DIT guarantee, Heap's DIT-listed data-processing instructions therefore run with operand-independent timing. Instructions on the path that are not DIT-listed are not covered by this note, and this note does not claim that Heap as a whole executes in constant hardware time.
- **Runtime14 v1.2.** No current caller sets DIT. Its CT result is therefore a control-flow and access-pattern result only. It makes no statement about data-processing timing.

The next release train states this in the claim wording itself: CT is defined as event-trace equality, and Arm's DIT guarantee is a named claim condition.

For how the current signed releases are graded (CT0, CT1, CT2), see [GRADES](GRADES.md). Neither superseded release holds CT1.

## The "loaded as reviewed" wording in Runtime14 v1.2

The Runtime14 v1.2 claim includes the parenthetical "(GB10.Runtime14LoadedAsReviewed)". This is an informal label, not a key in the premise manifest. That the image is loaded as reviewed is an assumption, carried by the manifest's loader-image obligations, which are attested only at deployment. The next Runtime14 release states this explicitly in the claim text.

## Correction: DIT coverage of loads and stores in the D273 claims

The D273 claims for secp CT0/CT0-DIT and route 7 (memcpy, memset, memmove) said that byte and word loads and stores are not covered by Arm's Data Independent Timing (DIT) guarantee. That statement was wrong. Those load and store forms are on Arm's DIT list (Arm ISA 2025-09; Arm ARM K.a). The D273 signatures remain valid over their bytes, but the statement is withdrawn. The current versions (secp CT v2, route 7 v2), which supersede them, use the corrected wording: load/store data latency is excluded unless the instruction is DIT-listed, and addresses are covered by CT0.
