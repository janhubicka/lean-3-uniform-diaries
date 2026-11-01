import ThreeUniformDiaries.DiaryFiniteInducedMeetsIntoCountable

/-!
# Track B: mixed auxiliary meet transport from an honest finite diary copy

The upper-bound ATR inclusion cannot be obtained merely by applying
the full two-type meet identity: full two-meets are the minimum of
both coordinate singleton meets and the auxiliary meet. A singleton
coordinate can mask an auxiliary disagreement.

Instead reuse the already verified E1--E5 marker-small-or-capped
proof from the finite lower bound. A full finite meet embedding
already supplies all fields of a finite leaf preembedding, with
the harmless target bound f(n) obtained from global monotonicity.
The verified induced mixed-aux transport then applies directly.

This is intentionally ONLY the mixed (split-containing) auxiliary
case; leaf-only and marker-containing pairs remain separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- An exact finite diary meet embedding automatically satisfies the
leaf-preembedding interface with an honest upper image bound. No
additional target-size or genericity hypotheses are necessary. -/
theorem FiniteMeetEmbedding.asFiniteLeafPreembedding
    {A T : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}
    (E : FiniteMeetEmbedding A T n f) :
    FiniteLeafPreembedding A T n (f n) f := by
  refine {
    strictMono := E.strictMono
    marker_zero := E.marker_zero
    marker_one := E.marker_one
    marker_two := E.marker_two
    image_bound := ?_
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro u hu
    exact E.strictMono hu
  · intro u hu3 hu
    exact ⟨E.leaf_iff u hu3 hu,
      E.oneSplit_iff u hu3 hu,
      E.twoSplit_iff u hu3 hu⟩
  · intro a b c hab hbc hc _ _ _
    exact E.edge_iff a b c hab hbc hc
  · intro a b ha3 han hb3 hbn _ _
    exact E.oneMeet a b ha3 han hb3 hbn
  · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
      _ _ _ _
    exact E.twoMeet a b c d hab hcd
      ha3 han hb3 hbn hc3 hcn hd3 hdn

/-- Every mixed comparison of two ordered nonmarker pairs has its
EXACT auxiliary meet transported under an induced full finite diary
embedding into a countable full diary.

The input \`FiniteMeetEmbedding\` includes exact ordinary one- and
two-meets; the substantive implication to exact AUXILIARY meets
depends on the E1--E5 marker-small-or-capped proof. -/
theorem FiniteMeetEmbedding.mixedAuxMeet_in_countable
    {A T : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DT : RoleDiary T)
    (E : FiniteMeetEmbedding A T n f)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (han : a < n)
    (hbn : b < n)
    (hc3 : 3 ≤ c) (hcn : c < n)
    (hdn : d < n)
    (hSomeSplit :
      (IsDiarySplit A a ∨ IsDiarySplit A b) ∨
      (IsDiarySplit A c ∨ IsDiarySplit A d)) :
    T.auxMeetLevel (f a) (f b) (f c) (f d) =
      f (A.auxMeetLevel a b c d) := by
  exact finite_induced_mixed_auxMeet_in_countable
    DA.prediary DT E.asFiniteLeafPreembedding E.edge_iff
    a b c d hab hcd ha3 han hbn hc3 hcn hdn hSomeSplit

end DiaryLeafPriority
end ThreeUniformDiaries
