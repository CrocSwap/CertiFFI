# Signed release changelog

Only the current releases are shipped. Earlier signed-off versions are listed here so their identities stay traceable.

## Current

| Release | Claim SHA256 | Signed payload SHA256 | Premise manifest | Signature |
|---|---|---|---|---|
| Heap v1.3 | `e871d8baad7aad6b0ebcd7dfdc817473c816f0158f6852f6b53fcd973705c662` | `ab855b46af9cd5ef6bf140a21b3217c01058768a3ca313d1b336b1d80a11a015` | `fea4a431…` (in payload) | `heap-v1.3/SIGNING-PAYLOAD.json.sig` |
| Runtime14 v1.4 | `559e9dc769d94214961cdbab426ea25750a3e2a578b139ddf69b27347cfd7728` | `31840e8c004478c4a608db9b246497b2e1747e340a063b52c7f4a106804952d1` | `784d494e…` (in payload) | `runtime14-v1.4/SIGNING-PAYLOAD.json.sig` |
| secp CT v2 (CT0, CT0-DIT, CT1, CT2; 32 shims) | `3276c7495c6bd117e0581d4269b17384ff48c922d4fa9dcdff365beb9ef9def6` | `5a6b3bfdb266118c7df783f07625fd9cd5e1c37424190e9cfa6d6730e1a8f603` | `05604f17…` (in payload) | `secp-ct-v2/SIGNING-PAYLOAD.json.sig` |
| route 7 memcpy v2 | `3c7ef211c0bd99ca0146b1a118620ba0dcf0b844ca606a4dad0c5a026dc2d91c` | `582b9158b7379cf86430c1ca2ee5da42b5e2f5f0b47a63fe87d4fd3f15bd1a4c` | `14cfe93d…` (in payload) | `route7-memcpy-v2/SIGNING-PAYLOAD.json.sig` |
| route 7 memset v2 | `4dc57c350479e1972fcd87e44737009b93eac042ef55f0f5d724ea2c073ac84a` | `9141b5b0fa77109efa217abd5e12f8fc5445b66ddb7caeaddf6dab077db6ee5f` | `1d66f3fb…` (in payload) | `route7-memset-v2/SIGNING-PAYLOAD.json.sig` |
| route 7 memmove v2 | `5bc51462a50ec5d80709bba43b2bd8611ffb3d8118afb63cb3f20d9fd7fd5771` | `90d8d8dda66cafb28289aea27cf068ad3457a67a5069a80421b414fdd32c15da` | `3aaa4ffb…` (in payload) | `route7-memmove-v2/SIGNING-PAYLOAD.json.sig` |
| secp shim v1 (first release, image-hash corrected re-sign) | `22b1831da64c8c0befa5204fbd9585bb30784a07b9ad87b406b88229c1652bb0` | `7ee1f1d954f109efc32076df3a7ee6b8608af43b7ba9d939619f072c1f3a831e` | `0c5edf7c…` (in payload) | `secp-shim-v1/SIGNING-PAYLOAD.json.sig` |

All seven payloads are signed with the release key in [`allowed_signers`](allowed_signers):
- principal `doug-armcert-release`;
- namespace `armcert-release-claim`;
- ED25519 key `SHA256:tmGDiCd6QUiSPxn2Ke9fsZes4nf72HGkS6wynGHcj6Q`.

Changes in the D274 versions (Heap v1.3, Runtime14 v1.4, secp CT v2, route 7 v2):
- the constant-time grades are stated in the security-grades v2.1 form (every event recorded; runs stated to the return, or to a stated stop or abort point), with CT2 residue results and, for secp and route 7, CT1;
- secp and route 7 name their distinct-secret witness theorems, with the SHA-256 of each witness statement, in the signed claim;
- every claim says that speculative execution (including straight-line speculation) is not addressed and that all grades concern the architectural (Sail) semantics;
- new premises: the return address lies outside the routine's code (secp, route 7), callers enter with PSTATE.DIT = 1 (route 7 CT1), and the secp load base is below 2^54 (a loader obligation, discharged from the TCR_EL2.T0SZ configuration rows);
- five configuration authority keys are renamed to the `ArmARM-RAZ` authority, values unchanged;
- the D273 statement that byte/word loads and stores are not DIT-covered is withdrawn (see [NOTES](NOTES.md)).

## Superseded

These versions are not shipped. Heap v1 and Runtime14 v1/v1.1 were signed off before the release-key scheme existed. Heap v1.1 and Runtime14 v1.2 were signed with the release key (D266), and the first secp shim v1 payload under D272; their payloads and signatures remain verifiable.

| Version | Seal SHA256SUMS digest | Superseded by | Reason |
|---|---|---|---|
| Heap v1.2 | payload `626c96861d4d898406b819b79ab42adbc08353dc2dc812065fc20ba13a01d10f` (signed; claim `70649820…`) | Heap v1.3 | D274 reseal: CT0 in the v2.1 form, CT2.R0, SLS non-claim, RAZ authority keys |
| Runtime14 v1.3 | payload `21ddb5a36d79b39e746ff039f988bfeee53d05dbe9fc27c627b9a506f81be970` (signed; claim `e1b2c0a3…`) | Runtime14 v1.4 | D274 reseal: CT0 in the v2.1 form, CT2.R0 findings, SLS non-claim, RAZ authority keys |
| route 7 memcpy / memset / memmove v1 | payloads `bd11a94b…` / `753f214a…` / `37febd3b…` (signed under D273; never shipped in this export) | route 7 v2 | D274: CT1 and CT2 added, CT0 stated to the return, witnesses bound; corrects the D273 DIT load/store statement |
| secp CT0/CT0-DIT v1 | payload `5e920591…` (signed under D273; never shipped in this export) | secp CT v2 | D274: CT1 and CT2 added, every grade stated to the return, c00 witnesses bound; corrects the D273 DIT load/store statement |
| secp shim v1 (as first signed) | payload `a886b8ec93dc477f73f458ad611e93b6f169f5563ffc2800d9c35ab7ba7d4cd2` (signed; claim `7f5555b2…`, manifest `04a22a5d…`) | secp shim v1, corrected re-sign | The manifest's `reviewed_image_sha256` held a placeholder (`96ca2c45…`) instead of the reviewed ELF's hash `d036c327…`, which the claim text and the manifest's `reviewed_image_elf` already stated. The re-sign changes that field and the digests derived from it: the sealed-manifest pointers in 10 ratification records, the manifest digest, and the claim's citation of it. Premises, roots and theorems are unchanged. |
| Heap v1.1 | payload `8009f8432703d89403ceddb4cc61dacc590b0ed0c0959b40e3c5a539f4dad60c` (signed) | Heap v1.2 | Next-train reseal: timers as per-entry data; explicit caller buffer precondition and no-double-mmap obligation; 16 features at TRM grade; neutral names |
| Runtime14 v1.2 | payload `924c3cf215265355a49f99476ed0836c3248defe6a93945e368c0e8a57da3013` (signed) | Runtime14 v1.3 | Next-train reseal: timers as per-entry data; explicit proof-only classes; 16 features at TRM grade; neutral names |
| Heap v1 | `62bdc12069ea6f59ca18d5ef5f7ce2944c92788d68191b60495655d27524b65f` | Heap v1.1 | Assumed FEAT_MTE2 absent. The deployment processor implements MTE2. v1.1 holds whether MTE2 is present or absent. |
| Runtime14 v1 | `c8bd2af37d4fc68cfbc03e878f8628e953777d344e8a8f32ebf2990fc7e1e110` | Runtime14 v1.1 | Carried a hidden state-universal premise. v1.1 replaced it with derived coherence. |
| Runtime14 v1.1 | `401de26b51d7cd1110ee74b927cf767c1e911f88ea908ca139b676af22ffece0` | Runtime14 v1.2 | Assumed FEAT_MTE2 absent (as Heap v1 did). |

The theorems in superseded versions remain kernel-checked under their own premises. They are withdrawn because those premises do not match the deployment machine.

## Notes

See [NOTES.md](NOTES.md) for what "constant-time" means in the current signed claims (model event-trace equality; the DIT condition for hardware timing).

## Source note: one shared module

`TranslateSpan.DefaultEntryMem` was sealed with slightly different bytes in two releases.
- Runtime14 v1.3's copy has one extra line, `set_option maxHeartbeats 200000 in`. This raises an elaboration resource limit and does not change kernel terms.
- secp shim v1's copy lacks that line.

This export carries the Runtime14 version, in `ReleaseShared`. The kernel-identity check for secp under that version (rebuild the downstream secp modules, then dump and compare constants against the sealed secp build) is **required before any publication**. Status: module-level check **passed**. dfc1 dumped the module's 32 constants (name, type, value) from each sealed build, and the sorted dumps are identical (5657011288e37d4e both); the `.olean` files differ only by 16 bytes of metadata (export-d272-checks-v1). End-to-end check **passed** as well (Xlate, receipt dem-check). All 1,770 secp modules were rebuilt fresh with the Runtime14 version swapped in. The kernel dump covers 68,893 constants (module, name, type hash, value hash) plus 32 root axiom lines, and is byte-identical to the dump of the sealed secp build (sha256 c605db4b… both). All 32 roots use only `propext`, `Classical.choice` and `Quot.sound`.

That intent was not met in D274: the secp CT v2 build again compiled secp's own copy of this module (without the extra line). This export still carries the Runtime14 version in `ReleaseShared`; the kernel-identity check for secp CT v2 under that version is part of the export parity check before publication. Status: **passed**. The full-value kernel dump of the secp CT v2 build from this export (303,129 constants, theorem bodies included) equals the sealed build's dump except for source byte offsets recorded in one generated definition's metadata (`mergeContig.eq_def`, `_recAppPos`), which do not affect kernel checking; and the secp CT v2 manifest recompiled from this export equals the signed one byte for byte (below).

## Reproducing the signed manifests from this export

The premise manifest in each signed payload can be recompiled from this export with the release gate tool, policy and registry of record.
Two of the `.olean` files hashed in each signed manifest (`canonical_source_oleans`), `ReleaseProfile/MachineSource/WordRecipe` and `ReleaseProfile/GB10/SpecWitness`, contain a stored linter message that records the absolute path of the source file at build time. To reproduce the signed manifest digests exactly, compile these two modules from copies at the original build paths, listed in `releases/<release>/BUILD-PATHS.txt`; every other hashed module contains no path. Built elsewhere, only these two hashes (and the interpretation and canonical-source hash fields derived from them) differ; the proved statements, premises and authorities are identical (checked by recompiling all six manifests from this export with the release gate tool). The provider inventory recorded with each release build (`PROVIDER-PINS.json`, not shipped in this repository) is not part of the manifest digest; about 10% of those `.olean` files also contain build paths, so that inventory is not a reproduction target from another location. The next versions remove these stored messages, and the release gate checks that no hashed .olean contains an absolute path. Compile with plain `lean` (as the release gate tool does), not Lake: Lake passes the package name to Lean, which records it in every `.olean` (the prebuilt cache is built with Lake and therefore differs from the hashed `.olean` files in this way; see README).

- Heap v1.3, secp CT v2 and route 7 v2 (memcpy, memset, memmove): with the two modules above at their original paths, the recompiled manifests equal the signed ones byte for byte (sealed / ratified: Heap `3d33388c…` / `fea4a431…`; secp CT `725e16d2…` / `05604f17…`; memcpy `70065a25…` / `14cfe93d…`; memset `94746fb3…` / `1d66f3fb…`; memmove `adaa64b1…` / `3aaa4ffb…`).
- Runtime14 v1.4: the recompiled manifest differs from the signed one only in the names of hygienic bound variables. The sealed build compiled two module families under a directory prefix, and Lean writes the module path into generated names: `R14CTv21.*` under `rt2.src.`, and `CT2R14FS.*` (and the shared `CT2Core.*`) under `rt2.src-ct2.`. For example, the sealed `x._@.rt2.src-ct2.CT2R14FS.C00.729629076._hygCtx._hyg.139` is `x._@.CT2R14FS.C00.729629076._hygCtx._hyg.139` here. Reinserting the prefix after `._@.` and `._internal.0.` in the recompiled report reproduces the signed manifest exactly (sealed `3a44bf53…`, ratified `784d494e…`). With the two path-bearing modules at their original paths (above), the recompiled report maps onto the sealed one exactly in both directions, and recomputing from it gives the signed sealed manifest (`3a44bf53…`) and ratified digest (`784d494e…`) with no `.olean` substituted. Bound-variable names do not affect kernel checking. The next Runtime14 version is built from the package root, so its names match directly.

