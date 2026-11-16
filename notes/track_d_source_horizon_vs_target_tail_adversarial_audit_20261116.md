# Track D adversarial audit — source-horizon persistence is not target-tail persistence (2026-11-16)

Scope: **circulation/non-appendix** of `3-uniform-diaries`, Track D, countable diary-unavoidability/lower bound. This is an English-level audit; **no change to frozen `main.tex`**, and no new Lean theorem is claimed to have passed CI.

## Verified interface and the precise missing implication

Read together:

* `ThreeUniformDiaries/DiaryFullNewGeneratorProfileStabilisation.lean`: `finite_choice_persistent_of_downward_type` and `persistent_stage_has_stable_new_nonleaf_record`.
* `ThreeUniformDiaries/DiaryNonEscapeEquivalentToPersistence.lean`: `cofinalBoundedNextLeafImages_iff_not_uniform_escape`, `persistentSuccessor_iff_not_uniform_escape`.
* `ThreeUniformDiaries/DiaryGenericE5NestedHorizonNoCompactness.lean` (merged #1531).
* `ThreeUniformDiaries/DiaryFixedColourGenericE5HorizonNoCompactness.lean` (merged #1532).
* `ThreeUniformDiaries/DiaryPersistentInternalGapStableProfile.lean` (draft #1536 at audit time, Track A).

Fix a source leaf `m` and old support map `f`. Let
`R(v,n)` mean that there exists an **actual** reserved stage of source horizon
`m+1+n`, literally compatible with `f` on the old support, with new leaf
image `g(m)=v`. Restriction of a real stage gives

    n <= N and R(v,N) => R(v,n).

The needed boundedness premise is

    exists B, for every N there are n>=N and v<=B with R(v,n).

This implies existence of one fixed `v<=B` such that `R(v,n)` holds for
**every** n: use the finite palette `{0,...,B}` and the downward condition,
taking a cofinal witness at least as large as any specified n. The existing
persistent-successor/bounded-image theorem additionally promotes this to an
actual persistent **new stage**; one must use that theorem's full genuine
reserved-stage hypotheses, not substitute the leaf-only relation.

The remaining open step is to prove this boundedness premise from the
prescribed diary geometry (or equivalently to exclude uniform eventual
escape). Merely choosing a finite split profile, an old-E5 pattern, or a
single finite singleton colour does not establish it.

## Important non-transfer of the generic tail countermodels

PRs #1531/#1532 use

    GenericOldPairHorizonTail G A q N v := (N < v) and old-pattern conditions.

For a **fixed target vertex** v this relation fails by setting N=v; it is
deliberately impossible for one v to survive all N. By contrast, the genuine
reserved-stage relation above increases a **source** horizon; nothing in the
definition of actual compatibility imposes `n < g(m)`, or an analogous
condition that the image of the source leaf must exceed the source horizon.

Consequently #1531/#1532 rigorously refute the **abstract inference**
"arbitrarily rich decreasing target tails => a common target vertex".
They do **not** exhibit a genuine fixed source diary for which
`R(v,n)` has the same moving-target-cutoff behaviour, and they cannot by
themselves establish failure of the desired boundedness condition in an
actual diary. Their own docstrings correctly state this scope. Preserve
that qualification when describing the results in the manuscript.

A new proof based on those countermodels would need to establish, rather
than assume, a diary-induced inequality of the form `g(m)>h(n)` with
`h(n)->infinity` for **every compatible reserved stage**. There is no such
general inequality in the inspected interfaces.

## Why the newer Track A bounded internal-gap theorem is not the missing step

Draft #1536 fixes finitely many source positions `T` strictly between
**two previously supported vertices** `x<y`. A real old-compatible stage
maps them into the finite target interval `(f(x),f(y))`, and finite-choice
stabilizes their joint image vector. But the newly selected source leaf m
is not in such a previously fixed old interval in general. Thus this
argument does not furnish a bound on `g(m)`.

In particular, `exists fixed internal T-profile across all horizons`
cannot be silently strengthened to `exists fixed next-leaf image across
all horizons`. The source support and the coordinates stabilized must
be displayed explicitly in any proposed strengthening.

## Suggested exact next proof obligation

Work in the genuine `ReservedDiaryStage` relation and attempt a
**non-escape theorem** for every already persistent old source stage:

    For every persistent old f at source leaf m,
    there exists B such that for every N there exist n>=N and
    an old-compatible ReservedDiaryStage at m+1+n with g(m)<=B.

Equivalent test: negate the eventual-escape statement in
`persistentSuccessor_iff_not_uniform_escape`.

Try either (a) source-compatible amalgamation/fusion of the old split
record with one fixed bounded next-leaf candidate while preserving S1/S2
and E2/E3, or (b) an explicit source/target counterexample disproving
this statement. A generic old-E5 tail example alone is not (b).

**Validation status:** the reduction is checked against the named Lean
statements and quantifier order, but this note supplies neither a new Lean
kernel-checked theorem nor unconditional countable unavoidability. No
validation marker for the latter should be added to frozen main text.
