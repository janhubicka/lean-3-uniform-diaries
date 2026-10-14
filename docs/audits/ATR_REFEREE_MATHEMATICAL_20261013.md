# ATR referee A: mathematical statement audit (13 October 2026)

This is a separately scoped adversarial analysis, not an external human referee.

**Reviewed:** manuscript `main.tex` Theorem `thm:ramsey`; `ActualFiniteAuxRamsey*.lean`, `FiniteAuxEmbeddingImage.lean`, `FiniteAuxLocalEmbedding.lean`, `UniversalAuxBranchEmbedding.lean`.

- The finite source is `Fin (k+1)`, not the misleading zero-extended Nat graph; `toLocal_toFiniteImage` verifies the local finite embedding code has no tail restriction.
- A single self-embedding `u` is chosen **before** `∀ e`, with `u∘e` represented by an appropriate protected refinement. The colour is constant on those actual finite images.
- The heterogeneous boundary-product HL premise is discharged by `boundaryProductHL_unconditional`, not an axiom.
- Previously the final endpoint required caller-selected `E, phi, hphi`; `exists_universal_auxEmbedding` already provides them. The new endpoint `actualFiniteAuxRamsey_matchingPrefix` removes this unused external input.
- **Remaining scope distinction:** manuscript quantifies over all finite A; Lean assumes `A.truncate n = G.graph.initialSegment n`. For incompatible prefixes, there cannot be a fixed-prefix embedding, so a separate formal vacuity lemma would finish the literal all-A formulation. Keep manuscript marker orange until that lemma is checked.
- Lean allows `n ≤ |A|`, covering the published `n < |A|` case.

Do not replace the genuine finite colouring with a colour on arbitrary infinite zero-extensions.