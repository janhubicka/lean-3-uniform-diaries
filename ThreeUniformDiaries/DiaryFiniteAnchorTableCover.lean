import ThreeUniformDiaries.DiaryFinitePositiveAnchorEquivalence
import ThreeUniformDiaries.DiaryFiniteExactFlipCoverCertificate
import ThreeUniformDiaries.DiaryFiniteFlipTransitivity

/-!
# Exact finite canonical flip-cover certificate using only positive anchors

The already verified finite table-cover criterion enumerates
(1) genuine source flip codes P of A,
(2) bounded protected embeddings f:P->B,
(3) genuine target flip codes T of B.

Its last check was equality of the entire induced T-pullback
edge table with the baseline A. By the new positive-anchor
equivalence, this is equivalent to checking just ONE positive
E2 incidence at each genuine one-split and ONE positive E3
incidence at each genuine two-split of the source.

The important point is that every candidate P->B becomes a
genuine LEAF preembedding A->T for EVERY target flip T:
first transport P->B through T and then use the genuine
source flip P->A. Thus the anchored completion theorem
applies without assuming inducedness of the selected copy
under T, without independent flip controls, and without
a fixed permutation of chosen source embeddings.

This theorem is an exact, mathematically FINITE certificate
for any fixed A,B. It still does NOT bound the size of a
finite absorber B for arbitrary non-rigid A.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The small collection of tests remaining after a finite
source leaf preembedding has already been constructed:
one positive source E2 leaf at each 1-split and one positive
source E3 ordered leaf pair at each 2-split must remain
positive at their images in the target. -/
def FiniteSplitAnchorsPreserved
    (A T : Ordered3Graph Nat) (n : Nat) (f : Nat → Nat) : Prop :=
  (∀ s : Nat, IsOneSplit A s →
    ∃ a : Nat, IsLeaf A a ∧ s < a ∧ a < n ∧
      A.edge 0 s a ∧ T.edge 0 (f s) (f a)) ∧
  (∀ s : Nat, IsTwoSplit A s →
    ∃ a b : Nat, a < b ∧ b < n ∧
      IsLeaf A a ∧ IsLeaf A b ∧ s < a ∧
      A.edge s a b ∧ T.edge (f s) (f a) (f b))

/-- A canonical source-flip code plus a fully protected
bounded source-flip copy in B yields a bounded LEAF
preembedding of the ORIGINAL source A in ANY genuine
target flip T, without presuming the map stays induced. -/
theorem finiteCanonicalFlipEmbeddingTable_leafPreembedding_in_targetFlip
    {A B T : Ordered3Graph Nat} {n k : Nat}
    (p : FiniteDiaryEdgeCode n × (Fin n → Fin k))
    (hp : p ∈ finiteCanonicalFlipEmbeddingTables A B n k)
    (FT : FiniteDiaryFlip B T k) :
    FiniteLeafPreembedding A T n k
      (extendFiniteBoundedMap n k p.2) := by
  let P := finiteDiaryCodeGraph n p.1
  have hValid :=
    (mem_finiteCanonicalFlipEmbeddingTables_iff A B n k p).mp hp
  have hRaw : p.1 ∈ finiteSourceFlipCodes A n :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n p.1).mp
      hValid.1).1
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n p.1).mp hRaw
  have E : FiniteBoundedMeetEmbedding P B n k
      (extendFiniteBoundedMap n k p.2) := hValid.2.2
  exact (E.leafPreembedding_after_target_flip FT).of_source_flip
    FP.symm

/-- The exact finite certificate for strong second flip
absorption requires only split-positive anchor checks, NOT
all E2/E3 source edge bits or full induced-pullback equality.

The candidate pool consists of ALL genuine canonical
source-flip codes with ALL bounded protected embedding
tables into the baseline target B. Every genuine target
flip code must admit at least one candidate whose images
satisfy the anchor-positive test. Multiple candidates per
source flip are allowed and often necessary. -/
theorem absorbsEveryTargetFlipInside_iff_finite_anchor_table_cover
    {A B : Ordered3Graph Nat} {n k : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    AbsorbsEveryTargetFlipInside A B n k ↔
      ∀ tcode : FiniteDiaryEdgeCode k,
        tcode ∈ finiteSourceFlipCodes B k →
        ∃ p : FiniteDiaryEdgeCode n × (Fin n → Fin k),
          p ∈ finiteCanonicalFlipEmbeddingTables A B n k ∧
          FiniteSplitAnchorsPreserved A
            (finiteDiaryCodeGraph k tcode) n
            (extendFiniteBoundedMap n k p.2) := by
  rw [absorbsEveryTargetFlipInside_iff_finite_table_cover DA]
  constructor
  · intro hCover tcode ht
    obtain ⟨p,hp,hPull⟩ := hCover tcode ht
    let T := finiteDiaryCodeGraph k tcode
    let P := finiteDiaryCodeGraph n p.1
    let f := extendFiniteBoundedMap n k p.2
    have hValid :=
      (mem_finiteCanonicalFlipEmbeddingTables_iff A B n k p).mp hp
    have hRaw : p.1 ∈ finiteSourceFlipCodes A n :=
      ((mem_finiteCanonicalSourceFlipCodes_iff A n p.1).mp
        hValid.1).1
    have FP : FiniteDiaryFlip A P n :=
      (mem_finiteSourceFlipCodes_iff A n p.1).mp hRaw
    have FT : FiniteDiaryFlip B T k :=
      (mem_finiteSourceFlipCodes_iff B k tcode).mp ht
    have E : FiniteBoundedMeetEmbedding P B n k f :=
      hValid.2.2
    have Q : FiniteLeafPreembedding A T n k f :=
      finiteCanonicalFlipEmbeddingTable_leafPreembedding_in_targetFlip
        p hp FT
    have ETarget : FiniteBoundedMeetEmbedding
        (finiteDiaryPullbackGraph T n f) T n k f :=
      finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
        FP.target_diary E FT
    have EA : FiniteBoundedMeetEmbedding A T n k f := by
      simpa only [hPull] using ETarget
    have hAnchors :=
      (finite_leafPreembedding_boundedEmbedding_iff_positive_anchors
        DA FT.target_diary Q).mp EA
    exact ⟨p,hp,hAnchors⟩
  · intro hCover tcode ht
    obtain ⟨p,hp,hAnchors⟩ := hCover tcode ht
    let T := finiteDiaryCodeGraph k tcode
    let f := extendFiniteBoundedMap n k p.2
    have FT : FiniteDiaryFlip B T k :=
      (mem_finiteSourceFlipCodes_iff B k tcode).mp ht
    have Q : FiniteLeafPreembedding A T n k f :=
      finiteCanonicalFlipEmbeddingTable_leafPreembedding_in_targetFlip
        p hp FT
    have EA : FiniteBoundedMeetEmbedding A T n k f :=
      (finite_leafPreembedding_boundedEmbedding_iff_positive_anchors
        DA FT.target_diary Q).mpr hAnchors
    have hPull : finiteDiaryPullbackGraph T n f = A := by
      apply finiteDiaryPullbackGraph_unique
        T n f A DA.prediary.frame
      intro a b c hab hbc hcn
      exact (EA.toMeetEmbedding.edge_iff
        a b c hab hbc hcn).symm
    exact ⟨p,hp,hPull⟩

end DiaryLeafPriority
end ThreeUniformDiaries
