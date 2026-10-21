# Adversarial audit: canonical geometric flip feedback (21 October 2026)

## What is genuinely verified

Merged PR #821 exports `canonical_feedback_injective_of_ordered_ranked_causality` and
`absorbsEveryTargetFlipInside_of_ordered_ranked_causality`.
The first applies strong induction to **genuine increasing source triples**, not
the redundant raw Boolean table. The second applies the already checked
canonical-feedback reduction. The rank may have ties, provided a correction
at a triple only depends on source bits at *strictly* smaller-ranked triples.

The proof is logically conditional: it accepts a selected family of actual
finite meet-preserving copies, one for each canonical source flip, and it
accepts the ranked-causality premise for **each** genuine target flip. Neither
the coherent copy family nor its geometric causality is constructed there.
The independent merged PR #819 also excludes fictitious changes to
invariant leaf-only edge coordinates.

## The missing implication to verify in English before formalising

Fix a source finite diary `A`, a finite diary target `B`, and for each
canonical source flip code `c`, one bounded meet-preserving embedding
`f_c: A_c -> B`. Given an arbitrary actual target flip `T`, define its
canonical pullback feedback `F_T(c)`. The new theorem will deliver
injectivity if there is a **single rank on the genuine source triples**
such that, for all target flips `T` and all canonical source codes `c,d`,

    c and d agree on all genuine triples of rank < rank(i,j,z)

implies

    F_T(c)[i,j,z] xor c[i,j,z]
      = F_T(d)[i,j,z] xor d[i,j,z].

The rank must be fixed for the chosen family, *not* chosen separately
for each source code or changed during the induction. A target-flip
quantifier cannot be replaced by the identity target flip: identity
feedback is already injective and tests no geometric compatibility.

## Risks that remain open

1. **Circular source-dependent embeddings.** Even if the target edge
   at `f_c(i),f_c(j),f_c(z)` appears at a late diary level, the locations
   `f_c(i),f_c(j),f_c(z)` may themselves depend on the very bit
   `c[i,j,z]` being solved for. A time ordering of target vertices
   alone does not imply ranked causality for feedback.
2. **Coupled split data.** The source flip orbit is not a free cube.
   Showing independence for hypothetical single-bit flips is neither
   necessary nor sufficient unless those flips are genuine.
   Compare *actual canonical source codes* with equal smaller-rank
   genuine edge coordinates.
3. **Positive classes versus order.** V1/V2 witness coherence and the
   early-leaf uniformity obstruction still restrict how copies can be
   made compatible. The completed ordered-sum/joint-embedding theorem
   only gives separated copies, not the new causality property.
4. **Quantifier direction.** Finite joint embedding of all source
   flips says `forall c, exists f_c`; absorption needs
   `forall target flip T, exists c` whose pullback is the
   ORIGINAL unflipped source. The canonical feedback permutation
   would supply this direction, but only after injectivity is proved.

## Next concrete validation target

For a proposed geometric embedding family, first prove the **edgewise
difference formula on genuine triples**, with the choice of `f_c`
unfolded. Then derive the strict smaller-rank dependence. Independently
audit the proposed rank on small canonical source flip orbits,
including ties, marker coordinates, and source-split witness edges.
Do not promote a formal conditional theorem to a validated
unconditional lower-bound proof.

Circulation manuscript `main.tex` is frozen. This file records
validation obligations only and makes no editorial changes to it.
