import ThreeUniformDiaries.DiaryFiniteThreeTailAmalgam

/-!
# Four literal profile equalities imply native three-tail overlap

For two three-tail source pictures A and B, the first picture
lists exterior vertices (split, left leaf, shared central leaf),
and the second lists (split, shared central leaf, right leaf).

The one-position shift embeds the second source into the intended
four-tail amalgam. Its overlap consists precisely of
* the complete protected prefix;
* the common split vertex;
* the shared central leaf.

For a ternary relation, agreement on that overlap is equivalent
to FOUR families of actual increasing edge equalities:
1. all triples entirely within the protected prefix;
2. all prefix-pair edges ending at the split;
3. all prefix-pair edges ending at the central leaf;
4. all prefix/split/central-leaf edges.

This module proves that these four families suffice for the
literal ThreeTailOverlapCompatible predicate of the free
amalgamation theorem. The positive/negative diary source
compatibility already proved separately provides the needed
second, third and fourth profile comparisons after the
appropriate source compression. No auxiliary meet assertion
is manufactured at this stage.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- A source overlap is determined by its four transparent
families of ternary edge bits. All hypotheses concern actual
increasing triples of the two source pictures. -/
theorem threeTailOverlapCompatible_of_profiles
    (A B : Ordered3Graph Nat) (n : Nat)
    (hPrefix :
      ∀ x y z, x < y → y < z → z < n →
        (A.edge x y z ↔ B.edge x y z))
    (hSplit :
      ∀ x y, x < y → y < n →
        (A.edge x y n ↔ B.edge x y n))
    (hCenter :
      ∀ x y, x < y → y < n →
        (A.edge x y (n+2) ↔ B.edge x y (n+1)))
    (hMixed :
      ∀ x, x < n →
        (A.edge x n (n+2) ↔ B.edge x n (n+1))) :
    ThreeTailOverlapCompatible A B n := by
  intro x y z hxy hyz hz
  have hcases : z < n ∨ z = n ∨ z = n+1 := by omega
  rcases hcases with hbefore | hat | hnext
  · have hx : x ≤ n := by omega
    have hy : y ≤ n := by omega
    have hz' : z ≤ n := by omega
    simpa only [threeTailShift_prefix n x hx,
      threeTailShift_prefix n y hy,
      threeTailShift_prefix n z hz'] using
        hPrefix x y z hxy hyz hbefore
  · subst z
    have hx : x ≤ n := by omega
    have hy : y ≤ n := by omega
    have hzn : n ≤ n := le_refl n
    simpa only [threeTailShift_prefix n x hx,
      threeTailShift_prefix n y hy,
      threeTailShift_prefix n n hzn] using
        hSplit x y hxy hyz
  · subst z
    have hzn : threeTailShift n (n+1) = n+2 :=
      threeTailShift_firstLeaf n
    by_cases hylt : y < n
    · have hx : x ≤ n := by omega
      have hy : y ≤ n := by omega
      simpa only [threeTailShift_prefix n x hx,
        threeTailShift_prefix n y hy, hzn] using
          hCenter x y hxy hylt
    · have hyeq : y = n := by omega
      subst y
      have hx : x ≤ n := by omega
      have hn : n ≤ n := le_refl n
      simpa only [threeTailShift_prefix n x hx,
        threeTailShift_prefix n n hn, hzn] using
          hMixed x (by omega)

end Ordered3Graph
end ThreeUniformDiaries
