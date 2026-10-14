# Survey: 423 public `formalization.yaml` records vs. their repositories

Run 2026-10-13 with `fwcheck.py` over every public GitHub repository with a
`formalization.yaml` at its root, found by code search
(`filename:formalization.yaml path:/`; the list is `repos.txt`). The
per-repository output is not published; anyone can regenerate it with
`python fwcheck.py --survey survey/repos.txt --out results.jsonl` and
summarize it with `--summarize` and `stats.py`. Individual projects are not
named here. Organizations making public verification claims about
high-profile releases, and the standard's own example repository, are.

## What was checked

For each record, the claims it makes were compared with what the repository
shows, without building anything:

- `status.sorry_count` (+ `sorry_in_definitions`) against `sorry` tokens in
  the Lean sources, comments and strings stripped, comparator challenge files
  and test/doc/script directories excluded (and reported separately).
- `status.axioms` against `axiom` declarations in the sources; `native_decide`
  use noted against whether `Lean.ofReduceBool` is listed.
- Each `main_results[].declaration` against the named file (and the tree).
- Each `main_results[].comparator_config` against the config's `theorem_names`.
- Every GitHub Actions workflow's latest run on the default branch, with
  failure-streak length; housekeeping workflows (Dependabot, Pages, release)
  not treated as verification.
- Schema validity for the declared version (v0.3, v0.4 published).

Not checked: whether proofs are correct (the kernel's job), whether Lean
statements mean what the paper says (a human's job), or whether files outside
the build graph should count. The scan is of the source tree, not the build.

## Headline numbers

| | |
|---|---|
| records checked | 423 (349 v0.4, 48 v0.3, 26 older or unversioned) |
| clean (every checkable claim backed by the repository) | 380 |
| stale (record behind the repository, mostly a red workflow) | 28 |
| contradicted (record says X, repository shows not-X) | 15, mostly small |
| **no CI workflow at all, or none that has ever run on the default branch** | **123 (29%)** |
| latest build/verification workflow run is a failure | 21; 11 with 2+ consecutive failures; 12 with no success in their last 30 runs |
| records naming a comparator config | 177 |
| …of which with a passing workflow named comparator/kernel/verify/check | 40 |
| …of which with no CI at all | 55 |
| claim `sorry_count: 0` | 327; 5 contradicted by the source |
| custom `axiom` declarations in source but absent from `status.axioms` | 6, plus 6 where the record states no axioms at all |
| `native_decide` used | 25; 3 list `Lean.ofReduceBool` |
| `review.status` | self-assessed 168, agent-reviewed 106, author-verified 45, free text 41, none 32; anything naming a human or peer reviewer, 14 |

## The finding

The records are, overwhelmingly, accurate on the day they are read. The
problem is that almost nothing keeps them accurate.

A record is a statement about a moment: "zero sorries, standard axioms,
comparator config here, last verified then." In 29% of the records nothing
will ever re-check that statement, and among the records that do have a
verification workflow, 21 are currently red, 12 of them with no green run in
their last 30. Several have been red for three to four months with the record
unchanged. This is the failure mode of the repository that prompted the tool,
[thefalsework/papers](https://github.com/thefalsework/papers): comparator
workflow failing on every run from 2026-07-29 to 2026-10-12 because of an
unpinned dependency, Lean build green throughout, record reading "verified
2026-07-13" the whole time. It is not a rare case. It is a typical one.

Anthropic described the same shape in their own CI on 2026-09-14
([Malhotra, "Agentic coding is straining CI"](https://claude.com/blog/agentic-coding-is-straining-ci-heres-how-we-scaled-test-impact-analysis-at-anthropic)):
the dangerous failure of their test-selection service was not downtime but a
patch that "quietly let some test results go unrecorded, so the service ended
up selecting tests from stale data." When agents produce faster than people
review, the layer that breaks silently is the record of what was verified.

Specific, public, organizational claims the survey bears on:

- `openai/NavierStokesAndEuler` (2,085 stars, 2,659 Lean files) and
  `openai/ten-proofs` (214 stars) carry accurate records and no GitHub
  Actions workflow. Their verification status is true as of their last
  manual run and will not update.
- `anthropics/fermats-last-theorem` (1,270 stars, 60,478 Lean files, zero
  sorries outside the challenge file): the only workflow is the Pages deploy;
  the comparator link runs through challenge theorems named differently from
  the record's main results, so a reader cannot connect the two from the
  record alone.
- `mathlib-initiative/sum_product`, the standard's own example, does not
  validate against the v0.3 schema it declares (`automation.methods[].method:
  "multi-agent framework"` is not in the enum). 88 records fail the schema
  they declare, mostly on enum values; 26 declare a version with no
  published schema.

Human review is rare: 14 of 423 records name a human or peer reviewer.
"agent-reviewed" and "self-assessed" are the norm, and 41 records put free
text in the status field, several of them paragraphs describing what was
*not* reviewed. The format is being used honestly; it is just not being used
to say "a person checked this," because mostly no person has.

The outright contradictions are few and mostly small: a template with
`sorry_count: -1`; a textbook project whose exercise sorries outnumber its
stated count; three records whose main results name files that no longer
exist; six records listing only the standard axioms while declaring their
own. None looked like misrepresentation. All looked like a record written
once and not revisited.

## What follows

The fix is not a smarter checker. It is running the simple one every time.
`fwcheck` in a workflow step, failing when the record and the repository
disagree, is the whole intervention; it would have caught every stale case
above the week it happened. The tool is free and takes one line to add.

Maintainers whose verification workflow has been red for months were told
privately before this was written up.

## Caveats

- The sorry/axiom scan covers every `.lean` file in the tree, including files
  not in the build. Exclusions are by path convention and are reported in
  each line so a reader can disagree.
- Declarations generated by macros, or restated in challenge files under
  other names, show up as "unverifiable", not as contradictions.
- "No CI" means no active GitHub Actions workflow with a run on the default
  branch. Projects verified elsewhere would need to say so in the record; a
  few do, in free text.
- Code search only indexes default branches of indexed repositories; 423 is a
  floor.
