import ThreeUniformDiaries.DiaryFiniteInducedAllMeetTransport
import ThreeUniformDiaries.DiaryFiniteBoundedUniversality
import ThreeUniformDiaries.DiaryFiniteCanonicalFlipPullback

/-!
# A canonical source flip embeds with ALL meets into each target flip

A finite target flip B' of B changes split incidences and does
not generally admit the original A as an exact embedded diary.
The existing geometric pullback constructs a canonical finite
source flip P of A, induced RELATIONALLY from B' along the old map.

We now upgrade this to a FULL protected finite meet embedding
P -> B' with the SAME map.

The original embedding A -> B remains a leaf preembedding
A -> B'. Since P is a genuine source flip, all relevant
leaf-only data are unchanged, so P -> B' is a leaf preembedding.
The canonical pullback additionally reflects the entire source
edge/nonedge table. The newly checked induced-meet theorem then
supplies exact numerical singleton and full pair meets involving
all roles, including mixed split/leaf tuples.

Crucial distinction: this theorem supplies a suitable P varying
with B'. It does NOT show P=A, or that every target flip absorbs
the prescribed UNFLIPPED A. The constrained causal selection
needed for that last statement remains separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Replace the SOURCE of a finite leaf preembedding by one of
its genuine identity-on-vertices diary flips. The leaf-restricted
numerical and ternary data are unchanged, although arbitrary
split-positive edges and mixed meets need not be. -/
theorem FiniteLeafPreembedding.of_source_flip
    {A P T : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}
    (Q : FiniteLeafPreembedding A T n k f)
    (F : FiniteDiaryFlip A P n) :
    FiniteLeafPreembedding P T n k f := by
  refine {
    strictMono := Q.strictMono
    marker_zero := Q.marker_zero
    marker_one := Q.marker_one
    marker_two := Q.marker_two
    image_bound := Q.image_bound
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro u hu3 hun
    have hQ := Q.role_iff u hu3 hun
    have hF := F.role_iff u hu3 hun
    exact ⟨hQ.1.trans hF.1,
      hQ.2.1.trans hF.2.1,
      hQ.2.2.trans hF.2.2⟩
  · intro a b c hab hbc hcn haP hbP hcP
    have han : a < n := by omega
    have hbn : b < n := by omega
    have haA : IsLeaf A a :=
      ((F.role_iff a haP.1 han).1).mpr haP
    have hbA : IsLeaf A b :=
      ((F.role_iff b hbP.1 hbn).1).mpr hbP
    have hcA : IsLeaf A c :=
      ((F.role_iff c hcP.1 hcn).1).mpr hcP
    exact (Q.leaf_edge_iff a b c hab hbc hcn haA hbA hcA).trans
      (F.leaf_edge_iff a b c hab hbc hcn haA hbA hcA)
  · intro a b ha3 han hb3 hbn haP hbP
    have haA : IsLeaf A a :=
      ((F.role_iff a ha3 han).1).mpr haP
    have hbA : IsLeaf A b :=
      ((F.role_iff b hb3 hbn).1).mpr hbP
    calc
      T.oneMeetLevel (f a) (f b) =
          f (A.oneMeetLevel a b) :=
        Q.leaf_oneMeet a b ha3 han hb3 hbn haA hbA
      _ = f (P.oneMeetLevel a b) :=
        congrArg f (F.leaf_oneMeet a b han hbn haA hbA)
  · intro a b c d hab hcd
      ha3 han hb3 hbn hc3 hcn hd3 hdn haP hbP hcP hdP
    have haA : IsLeaf A a :=
      ((F.role_iff a ha3 han).1).mpr haP
    have hbA : IsLeaf A b :=
      ((F.role_iff b hb3 hbn).1).mpr hbP
    have hcA : IsLeaf A c :=
      ((F.role_iff c hc3 hcn).1).mpr hcP
    have hdA : IsLeaf A d :=
      ((F.role_iff d hd3 hdn).1).mpr hdP
    calc
      T.twoMeetLevel (f a) (f b) (f c) (f d) =
          f (A.twoMeetLevel a b c d) :=
        Q.leaf_twoMeet a b c d hab hcd
          ha3 han hb3 hbn hc3 hcn hd3 hdn
          haA hbA hcA hdA
      _ = f (P.twoMeetLevel a b c d) :=
        congrArg f
          (F.leaf_twoMeet a b c d hab hcd
            hbn hdn haA hbA hcA hdA)

/-- The missing upgrade: a finite leaf preembedding which is
also genuinely INDUCED on all finite increasing triples is a
full finite meet embedding, provided both endpoints have the
finite V/E pre-diary axioms. -/
theorem FiniteLeafPreembedding.toMeetEmbedding_of_induced
    {A T : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}
    (PA : FiniteRolePrediaryBlock A n)
    (PT : FiniteRolePrediaryBlock T k)
    (Q : FiniteLeafPreembedding A T n k f)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c)) :
    FiniteMeetEmbedding A T n f := by
  refine {
    strictMono := Q.strictMono
    marker_zero := Q.marker_zero
    marker_one := Q.marker_one
    marker_two := Q.marker_two
    edge_iff := hInduced
    leaf_iff := ?_
    oneSplit_iff := ?_
    twoSplit_iff := ?_
    oneMeet := ?_
    twoMeet := ?_
  }
  · intro u hu3 hun
    exact (Q.role_iff u hu3 hun).1
  · intro u hu3 hun
    exact (Q.role_iff u hu3 hun).2.1
  · intro u hu3 hun
    exact (Q.role_iff u hu3 hun).2.2
  · intro u v hu3 hun hv3 hvn
    exact finite_induced_all_oneMeet_preserved
      PA PT Q hInduced u v hu3 hun hv3 hvn
  · intro a b c d hab hcd
      ha3 han hb3 hbn hc3 hcn hd3 hdn
    exact finite_induced_all_twoMeet_preserved
      PA PT Q hInduced a b c d hab hcd
      ha3 han hb3 hbn hc3 hcn hd3 hdn

/-- The CANONICAL induced source flip of any target diary flip
is a bounded full finite meet embedding into that target flip,
along the original marker-fixing source map.

This is a genuinely stronger result than the earlier relational
pullback, but it does not imply embedding the original A itself. -/
theorem finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
    {A B B' : Ordered3Graph Nat}
    {n k : Nat} {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (E : FiniteBoundedMeetEmbedding A B n k f)
    (F : FiniteDiaryFlip B B' k) :
    FiniteBoundedMeetEmbedding
      (finiteDiaryPullbackGraph B' n f) B' n k f := by
  let P := finiteDiaryPullbackGraph B' n f
  have FP : FiniteDiaryFlip A P n :=
    finiteDiaryPullbackGraph_is_sourceFlip
      DA E.toMeetEmbedding E.image_bound F
  have Q : FiniteLeafPreembedding A B' n k f :=
    E.leafPreembedding_after_target_flip F
  have QP : FiniteLeafPreembedding P B' n k f :=
    Q.of_source_flip FP
  have hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (B'.edge (f a) (f b) (f c) ↔ P.edge a b c) := by
    intro a b c hab hbc hcn
    exact (finiteDiaryPullbackGraph_edge_iff
      B' n f a b c hab hbc hcn).symm
  have hEmbedding : FiniteMeetEmbedding P B' n f :=
    QP.toMeetEmbedding_of_induced
      FP.target_diary.prediary F.target_diary.prediary hInduced
  exact ⟨hEmbedding,E.image_bound⟩

/-- Every finite flip of a target containing A receives a full
bounded embedded copy of SOME genuine flip of A. The source
flip is canonically determined by the target flip and map. -/
theorem exists_sourceFlip_boundedEmbedding_of_targetFlip
    {A B B' : Ordered3Graph Nat}
    {n k : Nat} {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (E : FiniteBoundedMeetEmbedding A B n k f)
    (F : FiniteDiaryFlip B B' k) :
    ∃ P : Ordered3Graph Nat,
      FiniteDiaryFlip A P n ∧
      FiniteBoundedMeetEmbedding P B' n k f := by
  exact ⟨finiteDiaryPullbackGraph B' n f,
    finiteDiaryPullbackGraph_is_sourceFlip
      DA E.toMeetEmbedding E.image_bound F,
    finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
      DA E F⟩

end DiaryLeafPriority
end ThreeUniformDiaries
