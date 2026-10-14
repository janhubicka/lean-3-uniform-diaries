import ThreeUniformDiaries.DiaryPointedShapeTransport

/-!
# Two-tail diary envelopes: equality of induced shapes

When the leaf-pair singleton meet lies before the protected cut, the
pointed carrier has just two exterior vertices. Its induced triples
are determined by the two singleton profiles and their auxiliary
pair profile. Equal ordinary leaf-pair 2-types transfer these data
along any type-respecting embedding, even if its image is not convex.

This complements the complete two-tail ATR meet-preservation lemma;
neither theorem asserts the unproved minimal-envelope carrier
identification for arbitrary source diagrams.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Two enumerated prefix-plus-two-tail induced pictures agree on all
triples if their full pair type at the prefix agrees. -/
theorem pointed_two_tail_edge_agreement_of_pair_type
    (H : Ordered3Graph Nat) (f g : Nat → Nat) (n : Nat)
    (hfixf : ∀ t, t < n → f t = t)
    (hfixg : ∀ t, t < n → g t = t)
    (hpair : H.SameTwoTypeBelow n (f n) (f (n+1))
      (g n) (g (n+1)))
    (x y z : Nat) (hxy : x < y) (hyz : y < z) (hz : z < n+2) :
    (H.pullback f).edge x y z ↔ (H.pullback g).edge x y z := by
  change H.edge (f x) (f y) (f z) ↔ H.edge (g x) (g y) (g z)
  have hfirst : H.SameOneTypeBelow n (f n) (g n) := hpair.1
  have hsecond : H.SameOneTypeBelow n (f (n+1)) (g (n+1)) := hpair.2.1
  have haux : H.SameAuxTypeBelow n (f n) (f (n+1)) (g n) (g (n+1)) :=
    hpair.2.2
  by_cases hzpre : z < n
  · have hy : y < n := lt_trans hyz hzpre
    have hx : x < n := lt_trans hxy hy
    simp only [hfixf x hx, hfixf y hy, hfixf z hzpre,
      hfixg x hx, hfixg y hy, hfixg z hzpre]
  · by_cases hz0 : z = n
    · have hy : y < n := by omega
      have hx : x < n := lt_trans hxy hy
      simpa only [hz0, hfixf x hx, hfixf y hy,
        hfixg x hx, hfixg y hy] using
        (hfirst (a := x) (b := y) hxy hy)
    · have hz1 : z = n+1 := by omega
      by_cases hylow : y < n
      · have hx : x < n := lt_trans hxy hylow
        simpa only [hz1, hfixf x hx, hfixf y hylow,
          hfixg x hx, hfixg y hylow] using
          (hsecond (a := x) (b := y) hxy hylow)
      · have hy0 : y = n := by omega
        have hx : x < n := by omega
        simpa only [hz1, hy0, hfixf x hx, hfixg x hx] using
          (haux (a := x) hx)

/-- Equal 2-types of the leaf pairs in the source force equality of
the induced two-tail envelope shapes after any type-respecting
embedding. The two selected target enumerations fix the entire
protected prefix, including vertices skipped by the embedding. -/
theorem pointed_two_tail_shapes_after_type_embedding
    {H K : Ordered3Graph Nat}
    (ψ : Ordered3Graph.Embedding H K)
    (hψ : ψ.TypeRespecting)
    (i a b c d : Nat)
    (hia : i ≤ a) (hic : i ≤ c)
    (hab : a < b) (hcd : c < d)
    (hpair : H.SameTwoTypeBelow i a b c d)
    (f g : Nat → Nat)
    (hfixf : ∀ t, t < ψ i → f t = t)
    (hfixg : ∀ t, t < ψ i → g t = t)
    (hfA : f (ψ i) = ψ a)
    (hfB : f (ψ i + 1) = ψ b)
    (hgC : g (ψ i) = ψ c)
    (hgD : g (ψ i + 1) = ψ d)
    (x y z : Nat)
    (hxy : x < y) (hyz : y < z) (hz : z < ψ i + 2) :
    (K.pullback f).edge x y z ↔ (K.pullback g).edge x y z := by
  have hpairImage : K.SameTwoTypeBelow (ψ i)
      (ψ a) (ψ b) (ψ c) (ψ d) :=
    (hψ.two i a b c d hia hab hic hcd).mp hpair
  have hpairSelected : K.SameTwoTypeBelow (ψ i)
      (f (ψ i)) (f (ψ i + 1))
      (g (ψ i)) (g (ψ i + 1)) := by
    simpa only [hfA, hfB, hgC, hgD] using hpairImage
  exact K.pointed_two_tail_edge_agreement_of_pair_type
    f g (ψ i) hfixf hfixg hpairSelected x y z hxy hyz hz

end Ordered3Graph
end ThreeUniformDiaries
