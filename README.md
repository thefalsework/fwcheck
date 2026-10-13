# fwcheck

Does a repository's `formalization.yaml` say what the repository shows?

The [Mathlib Initiative record format](https://github.com/mathlib-initiative/formalization.yaml)
lets a Lean project state its sorry count, axioms, main results, comparator
configuration and review status. Nothing checks those statements against the
repository. `fwcheck` does, from the outside, without cloning:

| claim in the record        | evidence checked                                                     |
|----------------------------|----------------------------------------------------------------------|
| `status.sorry_count` (+ `sorry_in_definitions`) | `sorry` tokens in all `.lean` files, comments and strings stripped, comparator challenge files excluded |
| `status.axioms`            | no custom `axiom` declarations in source; `native_decide` use noted   |
| `main_results[].declaration` / `file` | declaration found in the named file                        |
| `main_results[].comparator_config` | config exists and lists the declaration (or notes the challenge name differs) |
| toolchain / Mathlib        | `lean-toolchain` and `lake-manifest.json` pins reported               |
| build status               | latest default-branch run per GitHub Actions workflow; failure streak length |
| schema                     | validates against the published schema for the declared version      |

Each line is `OK`, `STALE` (record behind the repository), `MISMATCH` (record
contradicted by the repository), `UNVERIFIABLE` (no evidence either way) or
`INFO`. The verdict is one line: `n contradicted, n stale, n unverifiable, n backed`.

It does not check proofs (the kernel does) and does not judge whether a Lean
statement means what the paper says (a human does).

## Use

```
python fwcheck.py owner/repo            # text report; exit 1 if anything is stale or contradicted
python fwcheck.py owner/repo --json
python fwcheck.py --survey survey/repos.txt --out survey/results.jsonl [--resume]
python fwcheck.py --summarize survey/results.jsonl
```

Needs Python 3.9+, `pyyaml`, `jsonschema`, and a GitHub token (`gh auth token`
or `GITHUB_TOKEN`) for rate limits and tarball downloads.

## Origin

Written after finding that [thefalsework/papers](https://github.com/thefalsework/papers)
had carried "comparator-verified, last passed 2026-07-13" in its record for
three months while its comparator workflow failed on every run from
2026-07-29. Every tool in the chain was correct; the record was stale and
nothing compared it to the CI. `survey/repos.txt` is the list of public
repositories with a root `formalization.yaml` as of 2026-10-13 (GitHub code
search, 423 repositories).
