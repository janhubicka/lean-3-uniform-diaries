import ThreeUniformDiaries.DiarySingletonCompression

/-!
# Equality of finite pointed envelopes from their type profiles

A pointed 3-tail envelope carries a full fixed prefix, one split
vertex and two ordered leaf vertices. The induced hypergraph on
that finite carrier is determined by:
* the three singleton types below the prefix;
* the three auxiliary pair types below the prefix; and
* the sole triple on its three terminal vertices.

This is a purely finite type-profile argument. Deriving those
profile equalities from the diary axioms and ordinary 2-type equality
is a separate structural obligation.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Two pointed prefix-plus-three-vertex pictures are the same
induced enumerated hypergraph when their singleton, auxiliary-pair,
and terminal-triple profiles agree. The two enumerations can skip
different target vertices outside the common full prefix. -/
theorem pointed_three_tail_edge_agreement
    (H : Ordered3Graph Nat) (f g : Nat → Nat) (n : Nat)
    (hfixf : ∀ t, t < n → f t = t)
    (hfixg : ∀ t, t < n → g t = t)
    (hSplit : H.SameOneTypeBelow n (f n) (g n))
    (hLeafA : H.SameOneTypeBelow n (f (n+1)) (g (n+1)))
    (hLeafB : H.SameOneTypeBelow n (f (n+2)) (g (n+2)))
    (hMA : H.SameAuxTypeBelow n
      (f n) (f (n+1)) (g n) (g (n+1)))
    (hMB : H.SameAuxTypeBelow n
      (f n) (f (n+2)) (g n) (g (n+2)))
    (hAB : H.SameAuxTypeBelow n
      (f (n+1)) (f (n+2)) (g (n+1)) (g (n+2)))
    (hTriple : H.edge (f n) (f (n+1)) (f (n+2)) ↔
      H.edge (g n) (g (n+1)) (g (n+2)))
    (x y z : Nat) (hxy : x < y) (hyz : y < z) (hz : z < n+3) :
    (H.pullback f).edge x y z ↔ (H.pullback g).edge x y z := by
  change H.edge (f x) (f y) (f z) ↔ H.edge (g x) (g y) (g z)
  by_cases hpre : z < n
  · have hy : y < n := lt_trans hyz hpre
    have hx : x < n := lt_trans hxy hy
    simp only [hfixf x hx, hfixf y hy, hfixf z hpre,
      hfixg x hx, hfixg y hy, hfixg z hpre]
  · by_cases hz0 : z = n
    · have hy : y < n := by omega
      have hx : x < n := lt_trans hxy hy
      simpa only [hz0, hfixf x hx, hfixf y hy,
        hfixg x hx, hfixg y hy] using
        (hSplit (a := x) (b := y) hxy hy)
    · by_cases hz1 : z = n+1
      · by_cases hypre : y < n
        · have hx : x < n := lt_trans hxy hypre
          simpa only [hz1, hfixf x hx, hfixf y hypre,
            hfixg x hx, hfixg y hypre] using
            (hLeafA (a := x) (b := y) hxy hypre)
        · have hy : y = n := by omega
          have hx : x < n := by omega
          simpa only [hz1, hy, hfixf x hx, hfixg x hx] using
            (hMA (a := x) hx)
      · have hz2 : z = n+2 := by omega
        by_cases hypre : y < n
        · have hx : x < n := lt_trans hxy hypre
          simpa only [hz2, hfixf x hx, hfixf y hypre,
            hfixg x hx, hfixg y hypre] using
            (hLeafB (a := x) (b := y) hxy hypre)
        · by_cases hy0 : y = n
          · have hx : x < n := by omega
            simpa only [hz2, hy0, hfixf x hx, hfixg x hx] using
              (hMB (a := x) hx)
          · have hy1 : y = n+1 := by omega
            by_cases hxpre : x < n
            · simpa only [hz2, hy1, hfixf x hxpre,
                hfixg x hxpre] using
                (hAB (a := x) hxpre)
            · have hx0 : x = n := by omega
              simpa only [hx0, hy1, hz2] using hTriple

/-- A full 2-type agreement of the leaf pairs supplies the two
coordinate 1-types and the leaf-pair auxiliary type needed in
the preceding finite pointed-envelope calculation. -/
theorem pointed_three_tail_edge_agreement_of_pair_type
    (H : Ordered3Graph Nat) (f g : Nat → Nat) (n : Nat)
    (hfixf : ∀ t, t < n → f t = t)
    (hfixg : ∀ t, t < n → g t = t)
    (hSplit : H.SameOneTypeBelow n (f n) (g n))
    (hLeafPair : H.SameTwoTypeBelow n
      (f (n+1)) (f (n+2)) (g (n+1)) (g (n+2)))
    (hMA : H.SameAuxTypeBelow n
      (f n) (f (n+1)) (g n) (g (n+1)))
    (hMB : H.SameAuxTypeBelow n
      (f n) (f (n+2)) (g n) (g (n+2)))
    (hTriple : H.edge (f n) (f (n+1)) (f (n+2)) ↔
      H.edge (g n) (g (n+1)) (g (n+2)))
    (x y z : Nat) (hxy : x < y) (hyz : y < z) (hz : z < n+3) :
    (H.pullback f).edge x y z ↔ (H.pullback g).edge x y z := by
  exact H.pointed_three_tail_edge_agreement f g n hfixf hfixg
    hSplit hLeafPair.1 hLeafPair.2.1
    hMA hMB hLeafPair.2.2 hTriple x y z hxy hyz hz

end Ordered3Graph
end ThreeUniformDiaries
