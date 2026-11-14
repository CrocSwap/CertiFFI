# Signed releases

Each directory contains these files:
- `CLAIM.txt`: the plain-English claim;
- `BUILD-PATHS.txt` (D274 releases): the original build paths of the two hashed modules that record a path (see CHANGELOG, "Reproducing the signed manifests");
- `SIGNING-PAYLOAD.json`: the claim plus the compiled premise manifest;
- `SIGNING-PAYLOAD.json.sig`: an SSH signature over the payload.

## Verify a signature (offline)

```sh
ssh-keygen -Y verify -f allowed_signers -I doug-armcert-release \
  -n armcert-release-claim -s heap-v1.3/SIGNING-PAYLOAD.json.sig < heap-v1.3/SIGNING-PAYLOAD.json
```

Then check that the payload's `claim` field equals `CLAIM.txt` byte for byte, and that `claim_sha256` is its SHA256.

## Two signature namespaces, one key

The same key (principal `doug-armcert-release`) signs two kinds of object, under separate SSH namespaces:
- `armcert-release-claim`: the release claims above (`SIGNING-PAYLOAD.json`);
- `armcert-release-cache`: the prebuilt-cache manifest `CACHE-SHA256.txt`, signed at publication.

A signature made for one namespace does not verify under the other, so a cache-manifest signature can never be presented as a claim signature, or the reverse. `allowed_signers` lists both namespaces for the one key.

## Reproduce the proofs

A worked-example reproduction path will be published when the standard Lake build of the provider fits the 10-minute budget. Until then, these signatures attest the claims and manifests only.

See [GRADES](GRADES.md) for the security grades each release holds (held, FAIL with findings, or not attempted), [CHANGELOG](CHANGELOG.md) for superseded versions, and [NOTES](NOTES.md) for clarifications of the previous signed claims.
