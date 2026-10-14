# ATR referee C: proof/API minimality (13 October 2026)

Separately scoped dependency/API audit, not an external human review.

- `ActualFiniteAuxRamseyUnconditional` unnecessarily imported `ATRUnconditionalScalarColour`. Replace this with the actual needed `UniversalAuxBranchEmbedding` import, and remove unused namespace opens.
- Remove the caller's `E, phi, hphi` from the **public wrapper**, not from the proved internal coding lemmas. The wrapper now invokes `exists_universal_auxEmbedding`.
- The separately named scalar unconditional colouring theorem remains a useful audited library endpoint. Do not delete it merely because the final Ramsey proof can invoke the conditional version with proved HL.
- In `lean-milliken` PR #142, the generic finite-colour Ramsey-space lemma was extracted, breaking an unnecessary transitive dependency of general heterogeneous Milliken on homogeneous Hales–Jewett.
- **Do not delete** the old homogeneous `StrongEmbedding ι` theorem merely because heterogeneous Milliken subsumes it mathematically: the corresponding equivalence with `GeneralTree.StrongSubtree`, including stems/refinement/colour objects, is not yet proved in Lean.
- Keep E0/E1/E2, finite/infinite `F_I` identity, rooted decoder, strong completion and finite embedding action. They are essential to avoiding invalid shortcut proofs.

Apply deprecation replacements only where reported, without mass `simp` rewrites or global linter disabling.