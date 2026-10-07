# lean-3-uniform-diaries

Lean formalization accompanying the 3-uniform diaries manuscript.

Current branch `formalize-aux-ramsey` follows the repaired proof of the
aux-type-respecting Ramsey theorem.

Formalized without `sorry` or `admit` so far:

- decomposition of an ordinary ordered 2-type into two 1-types and one
  auxiliary type;
- aux-type-respecting implies type-respecting at the type-agreement level;
- the manuscript-faithful canonical-code/Milliken transfer, explicitly factoring through the universal branch hypergraph K_I;
- a checked dependency on the unconditional Milliken theorem in
  `janhubicka/lean-milliken`.

The next layer is the concrete finite/infinite canonical code for the three
type trees and the transport from the vector-tree Milliken statement.

The equality of explicit finite 1-type and aux-type nodes with agreement of the corresponding edge types below a cut is checked in `TypeRepresentation.lean`.

Additional concrete lemmas: `PrunedTypeTrees.lean` proves that every coordinate-tree node has a child; `CanonicalAgreement.lean` proves preservation/reflection of type agreement at selected cuts. These do not by themselves establish the full auxiliary Ramsey theorem.

The next concrete pieces prove disjointness and simultaneous generic realization of (C1)/(C2), the prescribed triples through one new source vertex, uniqueness of type-tree successor parameters, and one-step type-agreement recurrences. The countable K_I embedding and exact meet-level preservation remain open.

The branch-hypergraph layer `InfinitePrefixes`, `BranchHypergraph`, `RelativeBranchHypergraph`, and `BranchCountability` checks the finite enumeration coding and the induced map g_H into K_I (including its countable carrier). It does not yet supply the order-respecting enumeration or the generic embedding φ : K_I → G, nor the exact-meet argument.
