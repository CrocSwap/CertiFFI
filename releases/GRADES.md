# Security grades of the signed releases

Grades follow the security-grades standard v2.1. Signed claim texts are not changed by this file. Where a claim's own wording is narrower, the claim governs.

## How to read the grades

Each signed release states, per security grade, one of: **held**, **FAIL** with findings, or **not attempted**. A grade's meaning is fixed by its statement template; a theorem's name alone never earns it. Every grade is about the architectural (Sail) semantics of the Arm model.

- **CT0: model-trace constant time.**
  - For two runs that agree on everything except the declared secret inputs, the full runs to return (or to a stated stop or abort point) have equal length and equal event records, and every event has a record.
  - Records cover: explicit data accesses (read or write, virtual address, size); instruction fetches and translation-table-walk reads and writes (physical address, size); translation start/end markers; ISB barriers.
  - No data values are recorded. It says nothing about caches, TLBs or prefetchers.
- **CT1: data-independent timing.** CT0, plus: every body step runs with PSTATE.DIT = 1 and is a DIT-listed instruction or public control; every executed instruction word is bound to the reviewed image; no SVE/SME is on the path; no step outside the DIT window has a secret operand. Hardware timing then follows only under **Arm's DIT timing contract (P3)**, a claim condition, neither proved nor measured. Load/store data latency is excluded unless the instruction is DIT-listed; addresses are covered by CT0.
- **CT2.R0–R4: no secret residue at return.** R0 general-purpose registers; R1 plus NZCV; R2 plus every byte written during the run except declared outputs; R3 plus SIMD registers; R4 plus full SVE state. Residue is architectural only. A FAIL lists exactly what retains secret-dependent data; **clearing it is the caller's responsibility**.
- **Non-vacuity.** A two-run grade marked **(identical-run only)** has no exhibited pair of admissible runs with different secrets; **(distinct-secret witness: …)** names the exhibited pair.
- **Not graded:** CT-S (speculation, including straight-line speculation), CT-T (microarchitectural timing), CT-P (power/EM), FR (fault resistance). Every D274 claim says so explicitly: none of these images is built with SLS hardening.

## Grades per current signed release

| Release | CT0 | CT1 | CT2 |
|---|---|---|---|
| Heap v1.3 | **held** (identical-run only); worked family to the return, 6 trap families to the abort at certiffi_trap; both runs under one caller source configuration | not attempted | **R0 held** (identical-run only): every register equal across runs or the caller's own; x9 holds the caller's DIT image. R1+ not attempted |
| Runtime14 v1.4 | **held** (identical-run only); c00–c07 to the return, c08–c13 to a fragment stop point | not attempted (no current caller sets DIT) | **R0**: c08, c11 held; others **FAIL**: c00–c03: x9; x20, x29 not proved equal (callee-saved restore outside the proved value plan). c04–c05: x8; x29 not proved equal (same reason). c06–c07: x8, x9; x20, x21, x29 not proved equal (same reason). c09/c10/c12/c13: x8. x0 in c00–c05 is the declared secret output |
| secp CT v2 (32 shims) | **held**; c00: distinct-secret witness (x1 limb 0, 0 vs 1); c01–c31: identical-run only | **held** (the shim sets DIT itself); c00: distinct-secret witness; c01–c31: identical-run only | **R0 FAIL** per family (Add x3–x8; Sub x3, x5–x8; Neg x2–x7; Double x2–x8; Mul x1–x8, x10–x15, x17; MulAlt x3–x8, x10–x16; Sqr x2–x8, x10–x16; SqrAlt x2–x8, x10–x14; Cmul x3–x8, x10; Mod4 x2–x7). x9 holds the caller's DIT image; cmul's x1 is returned unchanged |
| route 7 memcpy v2 | **held**, distinct-secret witness (n = 1, source byte 0x5a vs 0xa5) | **held** for callers that enter with DIT = 1 (none in the reviewed image); identical-run only | **R0 FAIL**: x4 (n > 0) not proved equal; depends on copied data |
| route 7 memset v2 | **held**, distinct-secret witness (fill 0x5a vs 0xa5) | **held** for DIT = 1 callers; distinct-secret witness | **held up to R3** (distinct-secret witness); R4 not graded |
| route 7 memmove v2 | **held**, distinct-secret witness (n = 1, 0x5a vs 0xa5, backward path) | **held** for DIT = 1 callers; identical-run only | **R0 FAIL**: x4 (forward) / x5 (backward), n > 0 |
| secp shim v1 (D272, corrected re-sign) | not attempted (no CT relation stated) | not attempted | not attempted |

Every CT0/CT1/CT2 grade on secp and route 7 is stated on a single "to the return" root, with the caller contract that the return address lies outside the routine's code (secp also: load base below 2^54, a deployment obligation).

## Changes since the previous signed versions

- **Correction.** The D273 secp CT0/CT0-DIT and route 7 claim texts said byte/word loads and stores are not covered by Arm's DIT guarantee. That was wrong: those load/store forms are DIT-listed in the pinned Arm text (ISA2025-09; Arm ARM K.a). The D274 texts correct it. The D273 signatures stand over their bytes; the D274 versions supersede them.
- Heap and Runtime14 move from "pre-v2 statement form" to CT0 held under the v2.1 template.
- New CT1 and CT2 grades for secp and route 7; new CT2 grades for Heap and Runtime14.
- Explicit non-claim on speculative execution / SLS in every D274 text.
- Configuration authority keys: 5 TRM rows renamed to the ratified `ArmARM-RAZ` authority (values unchanged).
