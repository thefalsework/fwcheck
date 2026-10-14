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

## Layers

Below the claim-by-claim findings, the report describes what happens to a
proof after `lake build` is green: the places where "verified" can quietly
stop being true. Each layer is structured data (`--json`) and one text line.

| | layer | what is recorded |
|---|---|---|
| 1 | rebuild | `lean-toolchain`; Mathlib revision, its commit date and age; whether the project's toolchain is the one that Mathlib revision was built with (same / patch-level / different); dependencies the lakefile tracks at a branch |
| 2 | checkers | which checker tools the CI invokes (`comparator`, `lean4export`, `landrun`, `nanoda`, `lean4checker`, `lean-action`) and whether each is pinned by sha, by tag, or not at all; third-party actions on floating refs |
| 3 | linkage | for each comparator config: every `theorem_names` entry declared in the challenge module *and* in the project, and every record main result that claims the config actually named in it; `complete` only when all four corners hold |
| 4 | statements | static triage of each main result's statement: kind, number of binders and arrows, first proof tactic, and whether the statement mentions a custom axiom, an `opaque`, or a `def` whose body is `sorry`; flags such as `trivial-proof`, `native_decide`, `closed-statement` |
| 5 | literature | `literature_dependencies` (statement, source) as declared; sources with relationship and author endorsement; whether `fidelity.divergences` is non-empty |
| 6 | review | reviewers that look like people rather than models; alignment table rows; files in the tree that look like review artifacts |
| 7 | freshness | when `formalization.yaml` last changed, how many commits have touched it, how far it lags the head commit, last CI success; any date/retraction fields present |
| 8 | citation | a referee's checklist derived from 1–7 (`build_pinned`, `ci_green`, `independent_check_green`, `checkers_pinned`, `record_matches_tree`, `linkage_complete`, `no_sorry`, `standard_axioms_only`, `statements_unflagged`, `literature_deps_declared`, `human_review_named`, `record_fresh`, …) with a score over the items that apply |

Layer 4 is triage, not judgment: a flag means a human should look, not that
something is wrong. Layer 8 is what a journal referee could ask for in one
line and get an answer to.

## Use

```
python fwcheck.py owner/repo            # text report; exit 1 if anything is stale or contradicted
python fwcheck.py owner/repo --json     # findings + layers as JSON
python fwcheck.py --survey survey/repos.txt --out survey/results.jsonl [--resume]
python fwcheck.py --summarize survey/results.jsonl [--csv survey/rows.csv]   # aggregates, plus one CSV row per repo
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
