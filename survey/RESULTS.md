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
| …of which with a workflow that actually invokes a checker tool | 78 (69 green, 7 red, 2 never run) |
| …of which naming a config that no workflow runs | 99 (53 with no CI runs at all) |
| repositories whose CI invokes a checker tool | 212; only 78 of them cite the config in the record |
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

## The layers below the record (run 2026-10-14)

A second pass with the same tool, now reporting eight "layers": what happens
to a proof after `lake build` is green, and where "verified" can stop being
true without anyone changing the record. Same 423 repositories, structured
output per repository (`--json`), aggregates below. Nothing was built; every
number comes from the source tree, the lake manifest, the workflow files,
the comparator configs, and the Actions API.

**1. Rebuildability.** 415 of 423 depend on Mathlib. Every one of them pins
Mathlib to a revision and uses the toolchain that revision was built with
(414 exact, 1 patch-level, 0 different). That part of the ecosystem works.
Pin age is the issue: median 56 days, 109 between three and six months, 33
over six months, 2 over a year. A project more than a few months behind
Mathlib will, in practice, never move forward, and will stop building the
day its toolchain's cache disappears. Pin age is the same whether or not the
project has a green CI (median 54 vs 56 days), so CI is not what keeps
projects current.

**2. Checker supply chain.** 212 repositories invoke an independent checker
from CI: `comparator` 210, `landrun` 92, `nanoda` 71, `lean4export` 44,
`lean4lean` 4. Only 78 of the 212 cite a comparator config in the record's
`main_results`, so the record under-reports independent verification about
as often as it over-reports it (99 records cite a config that no workflow
runs). This corrects an earlier line in this writeup that counted comparator
workflows by name and found 40. Of those, 176 pin `comparator` by commit sha, 34 in a way the
tool could not classify, and one pins `lean4lean` to a branch. `lean-action`
is pinned by sha in 113 workflows and by tag in 99. This is better than
expected and better than the project that prompted the survey was doing in
July. The 34 unclassified pins are mostly one templated workflow, so a
single fix would cover them.

**3. Linkage.** 177 repositories name a comparator config; 294 configs in
total. For 267, all four corners hold: every `theorem_names` entry is
declared in the challenge module *and* in the project, and every record
main result that cites the config is actually among its names. 18 configs
are cited by a main result that the config does not name (the challenge
restates the result under another name, and the record does not say which),
4 have names missing from the challenge module, 2 have names missing from
the project. A reader of those 18 cannot connect the record to the
verification without reading the Lean.

**4. Statements.** 2,615 main results declared, 2,571 located and triaged
statically. 271 are not theorems (`def`, `abbrev`, `instance`,
`structure`), but 254 of those are three repositories of one organization
that lists its library's definitions as results; outside that, 10
repositories do it. 33 main results have a one-line `rfl`/`simp`/`decide`
proof (a trivial statement or a computation). 9 directly invoke a custom
`axiom` in the proof term; all 9 are in one organization's mathematical
physics projects and all are declared in the record. 435 statements have no
binders at all; most are fine (`Irrational √2` has none), and the flag is
there so a reader knows where to look. None of this is judgment; it is the
list of places a human should read first.

**5. Literature.** 41 repositories declare literature dependencies, 194 in
total, and 15 of the 41 are one author. The field exists in the schema and
is nearly unused. Of 1,623 source entries, 734 leave `author_endorsement`
blank and 558 say `not-contacted`; 80 repositories have at least one source
whose author participated or endorsed. 327 declare divergences from their
source; 96 declare none.

**6. Review.** 111 records name at least one reviewer who looks like a
person rather than a model. **7 name a person who is not one of the
project's own authors or maintainers.** The rest is self-review with a name
on it. 326 records carry an alignment table and 179 repositories have a file
that looks like a review artifact, so the raw material for a second reader
exists more often than a second reader does.

**7. Freshness.** 119 records (28%) have been touched exactly once: written
at publication, never revisited. 298 records are within a day of the head
commit, 101 lag it by up to a month, 23 by more. 4 records carry any
date-like field (`lean_kernel_checked`, `builds_clean_date`), and none
carries a deprecation or retraction field. The standard has no place to say
"this was true as of" or "this is withdrawn", and so nobody says it.

**8. Citation.** A referee's checklist assembled from the above, scored over
the items that apply: 10 repositories above 90%, 181 between 75 and 90, 212
between 50 and 75, 19 below 50. The items most often failed, in order:
independent reviewer named (415), independent kernel check green (336),
human reviewer named (311), CI green (153), CI present (109).

Read together: the machine layers (pins, checkers, linkage) are in better
shape than the July incident suggested, and the human layers (literature,
review, freshness) are where almost everything is missing. The formats
exist; the fields are blank.

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
- Layer 4 sees only direct references in a statement or proof term; a
  transitive dependence on an axiom needs `#print axioms`, which needs a
  build. Layer 2 reads workflow files with regular expressions and reports
  "unknown" when it cannot tell how a tool is pinned.
- "Independent reviewer" means a named reviewer who is not listed under
  `project.authors` or `responsible_maintainers`; it says nothing about how
  thorough the review was.
- Declarations generated by macros, or restated in challenge files under
  other names, show up as "unverifiable", not as contradictions.
- "No CI" means no active GitHub Actions workflow with a run on the default
  branch. Projects verified elsewhere would need to say so in the record; a
  few do, in free text.
- Code search only indexes default branches of indexed repositories; 423 is a
  floor.
