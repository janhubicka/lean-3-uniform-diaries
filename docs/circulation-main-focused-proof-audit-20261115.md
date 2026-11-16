# Focused non-appendix circulation proof audit (15 November 2026)

## Why this is a separate CI gate

The complete `ThreeUniformDiaries` umbrella imports almost every locally developed module, including historical conditional strategies and adversarial counterexamples. Successful umbrella compilation and an all-module admission scan are strong integrity tests but cannot answer the more targeted question: *are the formal theorem endpoints actually cited by the frozen circulation body available with their own imports and the standard transitive axioms?*

`scripts/CheckCirculationAxioms.lean` deliberately **does not import the umbrella**. It imports only modules directly required by the current non-appendix manuscript's green annotations, the orange critical-path proof cores for BRD/unavoidability/upper, and four numerically decisive lower-bound dependencies, then prints the transitive axioms of every distinct exported theorem endpoint. The existing strict `scripts/check_axiom_log.py` rejects missing/duplicated reports, `sorryAx`, and any axioms other than `propext`, `Classical.choice`, `Quot.sound`.

The new workflow step is in `.github/workflows/lean.yml` **in addition** to the complete Lake build, full source-integrity audit, umbrella-wide theorem-axiom audit, and all three finite regressions. This does not automatically identify dead source files or prove every manuscript sentence equivalent to its Lean theorem.

## Exact source snapshot and marker census

This manifest was generated from:
- `janhubicka/3-uniform-diaries/main.tex` with Git blob `933a25e5b097730dc4200317f16abc5f7552f327`;
- the manuscript `validation.tex` source pin `9508b2bb25ec72f72a43d7640ead01500802da29`;
- the current Lean source's existing theorem-specific `scripts/CheckAxioms.lean` registrations.

It contains:
- 43 **green** manuscript marker OCCURRENCES, corresponding to 41 distinct checked theorem names (one exact-meet theorem is cited at three separate places);
- 21 **orange** critical-path marker occurrences, corresponding to 21 distinct conditional or absolute Lean theorem endpoints;
- four further numerical labelled-BRD LOWER-dependency endpoints directly supporting the noncircular proof;
- **66 distinct theorem-axiom endpoint requests** from **57 directly imported modules**, with NO import of the `ThreeUniformDiaries` umbrella.

The full circulation marker census remains: 43 green, 96 orange, three blue interface, 18 grey pending, and one upstream Milliken verified = 161. The focused script intentionally does not claim coverage of all 96 orange annotations as standalone main theorem statements. The 21 selected are exactly the five `thm:BRD` linked cores, six `thm:unavoidable` linked cores, and ten `thm:upper` linked cores. The external Milliken marker is validated independently by upstream and is not reclassified as local Lean code.

## Audit contract and safe maintenance

- **Green**: exact linked declaration is imported with its own source module and its transitive axiom report is checked. This does NOT automatically validate every nearby explanatory English argument.
- **Orange**: only the formal theorem endpoint itself is checked, NOT the printed manuscript theorem without that endpoint's explicit hypotheses. In particular, the countable relative `Safe` or future-horizon extension premises stay unproved.
- **Numerical BRD lower dependencies**: confirm the unconditional **finite-source canonical marked-colour** lower route, rather than replacing it with the missing countable diary-unavoidability theorem.
- On any change to the manuscript's marker list or `main.tex` blob, regenerate this snapshot, inspect new/removed endpoints against printed hypotheses, and run exact-head CI. Do not silently carry over a green marker across a theorem renaming.
- Do not infer proof usefulness/deadness from the broad umbrella or this narrow set alone: a module may be an internal dependency, an adversarial regression, or part of another independent track.
- Frozen circulation `main.tex`, `validation.tex`, and existing collaborator TODOs are untouched in this PR.

## What remains outside this gate

The full countable-source diary unavoidability, full diary-selfembedding upper/Ramsey theorem, and the new-source-image persistence/no-escape problem still require mathematical existence proofs. This audit cannot promote `thm:unavoidable`, `thm:upper`, `thm:Ramsey` or the printed uncorrected `thm:BRD` markers. The separate exact *ordinary numerical labelled big Ramsey degree* is already verified in the lean finite-ATR/finite-diary-colour chain, pending exact counting-convention wording in the frozen paper.

All outcome claims concerning this new gate should be made **only after exact-head full GitHub Actions has completed successfully**.
