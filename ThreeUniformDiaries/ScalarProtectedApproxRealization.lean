import ThreeUniformDiaries.ScalarApproxLevelRigidity
import Milliken.GeneralTree.Original1979Conditional

/-!
# Complete the strong-tree realization step once a finite ATR code is placed

The final scalar Milliken application needs not just a finite code
inside the selected infinite strong tree B, but a further strong
refinement X that realizes exactly that finite approximation while
preserving the first n protected source levels.

The general-tree 1979 realization lemma in lean-milliken already
produces X from carrier inclusion. Here we prove the precise
PROTECTED version needed by ATR, using the checked rigidity of
selected levels under equality of finite approximations.

Thus the only remaining application task at this interface is to
construct a finite image code *contained in B* and to identify its
genuine finite F_I decoder. No separate "extend a finite code to
an infinite scalar subtree" assumption is needed.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree

/-- If two genuinely arbitrary-branched strong trees agree on their
first k selected levels, then they also agree on their first n levels
for n ≤ k. This includes skipped ambient heights. -/
theorem initialPart_eq_of_larger_initialPart_eq
    {U : Milliken.AmbientTree}
    (X T : StrongSubtree U)
    (n k : Nat) (hnk : n ≤ k)
    (h : X.initialPart k = T.initialPart k) :
    X.initialPart n = T.initialPart n := by
  have hlevel : ∀ j : Nat, j < n → X.levels j = T.levels j := by
    intro j hj
    exact sourceLevels_eq_of_initialPart_eq X T k h j
      (lt_of_lt_of_le hj hnk)
  ext x
  constructor
  · rintro ⟨hx, j, hjn, hxl⟩
    have hxk : x ∈ X.initialPart k :=
      ⟨hx, j, lt_of_lt_of_le hjn hnk, hxl⟩
    have htk : x ∈ T.initialPart k := by
      rw [← h]
      exact hxk
    refine ⟨htk.1, j, hjn, ?_⟩
    rw [← hlevel j hjn]
    exact hxl
  · rintro ⟨ht, j, hjn, htl⟩
    have htk : x ∈ T.initialPart k :=
      ⟨ht, j, lt_of_lt_of_le hjn hnk, htl⟩
    have hxk : x ∈ X.initialPart k := by
      rw [h]
      exact htk
    refine ⟨hxk.1, j, hjn, ?_⟩
    rw [hlevel j hjn]
    exact htl

/-- The exact realization step required by scalar ATR:

A finite height-k approximation a contained in B, which agrees
through its first n selected levels with the protected initial
stem of B, can be realized by a genuine infinite refinement X
of B with both r_k(X)=a and r_n(X)=r_n(B).

The proof is unconditional on the heterogeneous Milliken theorem.
-/
theorem exists_refinement_realising_with_stem
    {U : Milliken.AmbientTree}
    (a : SFinite U k)
    (B T : StrongSubtree U)
    (n : Nat) (hnk : n ≤ k)
    (hcontained : a.carrier ⊆ B.carrier)
    (hTa : r k T = a)
    (hStem : r n T = r n B) :
    ∃ X : StrongSubtree U,
      X.Refines B ∧ r k X = a ∧ r n X = r n B := by
  obtain ⟨X, hXB, hXa⟩ :=
    exists_refinement_realising_general a B hcontained
  have hk : X.initialPart k = T.initialPart k := by
    have eqApproxs : r k X = r k T :=
      hXa.trans hTa.symm
    exact congrArg FiniteApprox.carrier eqApproxs
  have hn : X.initialPart n = T.initialPart n :=
    initialPart_eq_of_larger_initialPart_eq X T n k hnk hk
  have heq : r n X = r n T :=
    FiniteApprox.ext_carrier hn
  exact ⟨X, hXB, hXa, heq.trans hStem⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
