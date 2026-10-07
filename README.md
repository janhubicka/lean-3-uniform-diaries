# lean-3-uniform-diaries

Lean formalization accompanying the 3-uniform diaries manuscript.

Current branch `formalize-aux-ramsey` follows the repaired proof of the
aux-type-respecting Ramsey theorem.

Formalized without `sorry` or `admit` so far:

- decomposition of an ordinary ordered 2-type into two 1-types and one
  auxiliary type;
- aux-type-respecting implies type-respecting at the type-agreement level;
- the canonical-code/Milliken transfer step giving the Ramsey conclusion;
- a checked dependency on the unconditional Milliken theorem in
  `janhubicka/lean-milliken`.

The next layer is the concrete finite/infinite canonical code for the three
type trees and the transport from the vector-tree Milliken statement.
