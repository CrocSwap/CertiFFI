# CertiFFI

CertiFFI certifies machine-code functions against the IsaWitness Arm model in Lean. This export contains exactly the proof closure of the current signed releases:
- **Heap v1.3**
- **Runtime14 v1.4**
- **secp CT v2** (32 shims: CT0, CT0-DIT, CT1, CT2)
- **route 7 v2** (memcpy, memset, memmove)
- **secp shim v1**

It pins the model (ArmFull) and runtime (Sail) from [IsaWitness](https://github.com/CrocSwap/IsaWitness). It takes the Lean standard library from the Lean 4.35.0 toolchain.

| Package | Modules | Contents |
|---|---|---|
| `Provider` | 2,027 | Shared proof layers: step, value, memory, translation, bridge, observation and leakage |
| `ReleaseHeap` | 104 | Heap release modules (GB10 configuration source and Heap families) |
| `ReleaseRuntime14` | 663 | Runtime14 release modules |
| `ReleaseSecp` | 1,703 | secp shim v1 release modules (also used by secp CT v2) |
| `ReleaseSecpCT` | 585 | secp CT v2 modules (CT0/CT1/CT2 roots, witnesses) |
| `ReleaseRoute7` | 179 | route 7 modules (memcpy, memset, memmove) |
| `ReleaseShared` | 37 | Modules shared by more than one release |
| `releases/` | n/a | Signed claims, payloads, signatures, `allowed_signers`, grades, changelog and notes |

## What this export is
- **An allowlist.** Each module is in the import closure of a signed release root. Nothing else is exported.
- **The same code as the sealed releases.** The signed releases were sealed from already-renamed sources. Every exported module's code and string literals are byte-identical to the sealed sources; only comments and docstrings were rewritten. Every release root keeps its sealed axiom set, using only `propext`, `Classical.choice` and `Quot.sound`. Rebuilt from this export, every release's full kernel dump (all constants, theorem bodies included) matches the sealed build, and every signed premise manifest reproduces (see `releases/CHANGELOG.md`, "Reproducing the signed manifests").
- **Produced by generators, never edited by hand.**
  - Comments and docstrings were rewritten to remove internal references, except in the 14 canonical-source modules (`ReleaseProfile.GB10.{CallerDomain, Canonical, DomainWitness, FeatureSource, HeapContext, ManifestRows, ModelRegs, Producers, Source, SourceSpec, SpecWitness}`, `ReleaseProfile.MachineSource.{Coordinates, Recipe, WordRecipe}`). Those ship byte-for-byte as sealed, because the signed manifests hash their compiled files; a few internal labels (decision numbers, reviewer handles) therefore remain in their docstrings.
  - Identifiers were renamed by the published map.
  - Model diagnostic paths were rewritten by the published path map.
  - Every other code and string byte is unchanged from the sealed sources.
  - See `EXPORT-REPORT.json` and `SCAN-REPORT.json`.

## Renames and residuals
- **Identifiers are neutral.** Module and declaration names that carried historical internal labels are renamed by a published, injective map (`RENAME-MAP.json`, 131 name atoms). For example: `N1Entry145*` became `NativeEntry*`, `D236Frames` became `TagCheckFrames`, and `ArmCertWalkD142` became `ArmCertWalk`. The renames were applied before the D272 reseal and checked by rename-aware kernel parity against the unrenamed gated prefix and packages (IDENTICAL_MODULO_RENAME_MAP for all three releases).
- **Model diagnostic paths are neutral.** The assertion strings copied from the model use the same relative paths as the IsaWitness model. The model sources were relocated from internal build paths to these names; `MODEL-PATHMAP-v3.tsv` lists the neutral names.
- **Remaining string data.** Card IDs and configuration-catalogue row IDs still contain historical labels. They change with the regenerated catalogue in the next reseal.
- **Generated module names.** Some module names generated per card carry historical generator labels (for example `PipeLean_D234_SecpAdd_c00.*`). They are part of the sealed declaration names, so renaming them needs a reseal.
- **The signed payloads are immutable.**
  - `releases/*/SIGNING-PAYLOAD.json` carry historical premise keys and registry IDs, including decision-numbered keys and one `PROVISIONAL:` ID.
  - Editing them would invalidate the signatures.
  - They are replaced only by the next signed release.

## Using the prebuilt cache
The fastest way to check the releases is to depend on a release package and use the signed prebuilt cache:
1. In your project's `lakefile.toml`, require one release package (`ReleaseHeap`, `ReleaseRuntime14`, `ReleaseSecpCT`, `ReleaseRoute7`, `ReleaseSecp` or `ReleaseShared`) from this repository by git rev, with `subDir` set to the package name, and run `lake update`.
2. Download the archives named in `releases/cache/CACHE-SHA256.txt` from the assets of the `d274` release (https://github.com/CrocSwap/CertiFFI/releases/tag/d274) into a directory, and from your project root run `.lake/packages/<Package>/releases/cache/get-cache.sh <archive-dir>`. It works out which archives your package needs from the lakefiles. It first verifies the signature on `CACHE-SHA256.txt` (namespace `armcert-release-cache`, key in `releases/allowed_signers`), then every archive's SHA-256, and extracts nothing unless all pass.
3. `lake build` with the stock `leanprover/lean4:v4.35.0` toolchain. Nothing from the cache is rebuilt.

**Trust.** Lean does not re-check proofs inside imported `.olean` files, so this path trusts the archive builder. That is why the manifest is signed. To avoid trusting the archives, build from source (below).

**What the archives contain.** They were built with Lake from this repository at the neutral path `/tmp/CertiFFI`, with the per-file directive wrapper (below). They record that path in Lake trace and log files and in stored compiler messages of 1,426 `.olean` files (per archive: Provider 525, ReleaseSecp 489, ReleaseRuntime14 260, ReleaseRoute7 62, ReleaseSecpCT 43, ReleaseHeap 37, ReleaseShared 9, lean-sail 1, IsaWitness model 0); they contain no other path. The cache `.olean` files differ from the canonical `.olean` files hashed in the signed manifests by the Lake package name recorded in the module header and, for some modules, the neutral build path in stored compiler messages. The signed digests reproduce with the from-source recipe (plain `lean`, `BUILD-PATHS.txt`; see `releases/CHANGELOG.md`).

## Building from source
Each package directory is a Lake root (`lakefile.toml`, `Elab.async = false`, IsaWitness required by git rev). Build `Provider` first, then the release package you need.

**Ten modules need a per-file setting.** These modules carry a `Compile using EVAL_OPAQUE_CALLEES=ArmFull.Functions.BranchTo` comment, and the signed results were built with that variable set for exactly those files (setting it globally breaks other modules):
- `Provider`: `BR8.BCond`, `BR8.CBZ`, `NativeEntryCallerParts.BlPrefix`, `NativeEntryCallerParts.BlrPrefix`
- `ReleaseRoute7`: `LoopNative.Cbz64.Prefix`, `LoopNative.Cbnz64.Prefix`, `Route7Cbnz.BR`
- `ReleaseRuntime14`: `NativeR14B.BPrefix`, `NativeR14B.CbzPinsPrefix`, `NativeR14B.TbnzPinsPrefix`

Build with the wrapped toolchain, which applies a file's own directive and nothing else:
```sh
tools/make-wrapped-toolchain.sh                  # once; needs elan. Installs leanprover/lean4:v4.35.0 if needed and
                                                 # links it as the toolchain certiffi-wrapped-v4.35.0
cd ReleaseHeap && lake +certiffi-wrapped-v4.35.0 build   # or any package directory
```
The wrapped toolchain is the stock one except `bin/lean`, a shim (`tools/lean-wrapper.sh`) that sets `EVAL_OPAQUE_CALLEES` from the compiled file's own `Compile using` comment, clears any inherited `EVAL_*` variable, and refuses any other directive key. Tested on Linux aarch64.

**Warning: a stock build without the wrapper can succeed with different results.** Without the directive, `BlPrefix`, `BlrPrefix`, `LoopNative.Cbz64.Prefix`, `LoopNative.Cbnz64.Prefix` and `NativeR14B.BPrefix` fail (heartbeat timeouts). The other five compile without error, but each defines its `native` step function differently (`ArmFull.Functions.BranchTo` unfolded instead of opaque): `BR_BCondH.native` (`BR8.BCond`), `BR_CBZ.native` (`BR8.CBZ`), `BR_CBNZ.native` (`Route7Cbnz.BR`), `NativeR14B.CbzPinsPrefix_native` and `NativeR14B.TbnzPinsPrefix_native`. Their `complete` theorems have the same statements but then refer to a different definition of the same name. The signed results are for the directive build only, and downstream modules may fail or differ.

**Check after building:** `tools/check-directive.sh` lists every constant of the ten modules (name, kind, universe parameters, type and value hashes), hashes each list and compares it with `tools/DIRECTIVE-MODULES.sha256` (from the published cache). It does not depend on the build path or Lake. `OK` for all ten means the directive was applied. This detects an accidental build difference (for example, building without the directive); it is not a tamper-evidence mechanism (`Expr.hash` is a 64-bit structural hash, not a cryptographic one). Tamper evidence comes from the signed `CACHE-SHA256.txt` and manifest digests.

**Reproducing the signed manifest digests** needs plain `lean` (not Lake, which records the package name) and two modules compiled at their original paths; see `releases/CHANGELOG.md` and `releases/*/BUILD-PATHS.txt`.

**Checking the roots.** `#print axioms` on every theorem root of a release's `SIGNING-PAYLOAD.json` prints only `propext`, `Classical.choice` and `Quot.sound`. A few roots (`ReleaseProfile.GB10.CanonicalLiterals`, `Image`, `ProofOnlyClasses`, `SourceDomain`) are module or namespace authority roots, not constants; the release gate covers them.

## Status
- **Release:** the D274 signed releases. Kernel parity against the sealed builds and reproduction of every signed manifest were checked before publication.
- **Signatures:** these verify offline; see `releases/README.md`.
- **Next versions:** the directive becomes a Lean option, so a stock `lake build` reproduces without the wrapper; the stored-path messages are removed, and the release gate checks that no hashed `.olean` contains an absolute path.

## License
Apache-2.0 for first-party material; see `LICENSE`. Copyright (c) 2026 Crocodile Labs Inc.
