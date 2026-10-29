import ThreeUniformDiaries.DiaryFiniteCanonicalFirstS2CrossMeet
import ThreeUniformDiaries.DiaryFiniteCanonicalCrossTwoMeetFullTarget
import ThreeUniformDiaries.DiaryFiniteCanonicalTargetWithPrediary
import ThreeUniformDiaries.DiaryFiniteCanonicalExplicitFirstDifferenceSeparation
import ThreeUniformDiaries.DiaryFiniteExplicitFeedbackLiteralSeparation

/-!
# Strong finite flip absorption by the real canonical sign-rooted diary

For every finite full diary A, choose the genuine constrained orbit
of all its canonical flips. Construct the finite causal sign-rooted
V/E pre-diary, a single countable dummy-tail V/E completion, its
one-pass full diary, and the finite leaf-meet support of ALL source
flip leaf images. The resulting target B is one genuine FINITE
full diary, carrying explicit bounded exact-meet embeddings of all
source flips.

A target flip cannot collapse two original canonical source flips
after pullback. Distinct global Devlin signs remain distinct in
any target flip, while equal signs have a first genuine differing
S2 witness bit. Its two source branch copies have a literal full
pair meet at their shared causal two-split. This CROSSBRANCH meet
survives dummy-tail extension, one-pass full completion, and
finite leaf-meet compression. The target flip retains the common
2-split and therefore must assign opposite E3 incidences there.
Thus the explicit geometric feedback is injective on the REAL
finite canonical source orbit, hence surjective. The baseline
unflipped source appears as one pullback inside EVERY target flip.

No abstract independent Boolean cube and no arbitrary
Classical.choose copy maps are used. This is the complete
finite BOTH-DIRECTIONS flip property; it is not by itself a
formalization of the manuscript's final unavoidability theorem
or the corrected upper bound.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The source-fixed first differing S2 witness has the SAME
actual target split image in both canonical source branches,
and the two target ordered leaf pairs have exact full
pair-type meet at that genuine shared split. The auxiliary
dummy-tail V/E certificate used here belongs to the SAME bits
as the concrete final finite target and source maps. -/
theorem canonicalCausalOrbitFiniteTarget_firstS2CrossMeet
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (bits : Nat → Bool)
    (PT : RolePrediary (canonicalCausalCountableCarrier DA bits))
    (i j : FiniteCanonicalFlipIndex A n)
    (s : FiniteTwoSplitIndex A n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s.val.val =
      (finiteCanonicalSignRootedFamily DA).node j s.val.val)
    (hDiff :
      ((finiteCanonicalSignRootedFamily DA).signature i).2 s ≠
      ((finiteCanonicalSignRootedFamily DA).signature j).2 s) :
    let W := finiteSelectedS2Witness DA s
    canonicalCausalOrbitFiniteSourceMap DA bits i s.val.val =
      canonicalCausalOrbitFiniteSourceMap DA bits j s.val.val ∧
    (canonicalCausalOrbitFiniteTarget DA bits).twoMeetLevel
      (canonicalCausalOrbitFiniteSourceMap DA bits i W.a)
      (canonicalCausalOrbitFiniteSourceMap DA bits i W.b)
      (canonicalCausalOrbitFiniteSourceMap DA bits j W.a)
      (canonicalCausalOrbitFiniteSourceMap DA bits j W.b) =
      canonicalCausalOrbitFiniteSourceMap DA bits i s.val.val := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let W := finiteSelectedS2Witness DA s
  have hRank :
      finiteCanonicalSourceRankMap DA i s.val.val =
      finiteCanonicalSourceRankMap DA j s.val.val := by
    have hNode :
        finiteCanonicalNodeAt DA i s.val.val s.val.isLt =
        finiteCanonicalNodeAt DA j s.val.val s.val.isLt :=
      Subtype.ext hShared
    rw [finiteCanonicalSourceRankMap_of_lt DA i s.val.val s.val.isLt,
      finiteCanonicalSourceRankMap_of_lt DA j s.val.val s.val.isLt]
    exact congrArg
      (fun X : FiniteCanonicalSignRootedVertex DA =>
        (finiteCanonicalNodeIndex DA X).val) hNode
  have hSame :
      canonicalCausalOrbitFiniteSourceMap DA bits i s.val.val =
      canonicalCausalOrbitFiniteSourceMap DA bits j s.val.val :=
    canonicalCausalOrbitFiniteSourceMap_eq_of_sourceRank_eq
      DA bits i j s.val.val s.val.val s.val.isLt s.val.isLt hRank
  have hCausal :
      (finiteCanonicalCausalMarkerGraph DA).twoMeetLevel
        (finiteCanonicalSourceRankMap DA i W.a)
        (finiteCanonicalSourceRankMap DA i W.b)
        (finiteCanonicalSourceRankMap DA j W.a)
        (finiteCanonicalSourceRankMap DA j W.b) =
      finiteCanonicalSourceRankMap DA i s.val.val :=
    finiteCanonical_firstS2Bit_causes_crossTwoMeet DA i j s hShared hDiff
  have han : W.a < n := lt_trans W.hab W.hbn
  have hLeafIa : IsLeaf (F.graph i) W.a :=
    ((F.flip i).role_iff W.a W.ha.1 han).1.mp W.ha
  have hLeafIb : IsLeaf (F.graph i) W.b :=
    ((F.flip i).role_iff W.b W.hb.1 W.hbn).1.mp W.hb
  have hLeafJa : IsLeaf (F.graph j) W.a :=
    ((F.flip j).role_iff W.a W.ha.1 han).1.mp W.ha
  have hLeafJb : IsLeaf (F.graph j) W.b :=
    ((F.flip j).role_iff W.b W.hb.1 W.hbn).1.mp W.hb
  have hFullMeet :
      (canonicalCausalOrbitFiniteTarget DA bits).twoMeetLevel
        (canonicalCausalOrbitFiniteSourceMap DA bits i W.a)
        (canonicalCausalOrbitFiniteSourceMap DA bits i W.b)
        (canonicalCausalOrbitFiniteSourceMap DA bits j W.a)
        (canonicalCausalOrbitFiniteSourceMap DA bits j W.b) =
        canonicalCausalOrbitFiniteSourceMap DA bits i s.val.val :=
    canonicalCausalOrbitFinite_crossTwoMeet_of_causal
      DA bits PT i j s.val.val W.a W.b W.a W.b
      s.property s.val.isLt hShared
      W.hab W.hab W.hbn W.hbn W.hsa W.hsa
      hLeafIa hLeafIb hLeafJa hLeafJb hCausal
  exact ⟨hSame,hFullMeet⟩

/-- The strong BOTH-DIRECTIONS finite flip property for every
bounded finite diary A. One actual finite full diary B has:
(1) bounded induced all-numerical-meet copies of ALL genuine
    canonical source flips, and
(2) a bounded induced all-numerical-meet copy of the ORIGINAL A
    inside EVERY genuine finite flip of B.

All source and target flips are REAL full diaries; all maps
have their entire finite images inside the target's bounded
frame. The abstract conditional feedback injectivity premise
has been DISCHARGED by causal crossbranch first-difference
geometry and the exact explicit-map finite permutation proof. -/
theorem exists_finiteDiary_strong_both_flip_directions
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    ∃ (B : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock B k ∧
      (∀ A' : Ordered3Graph Nat,
        FiniteDiaryFlip A A' n →
        ∃ f : Nat → Nat,
          FiniteBoundedMeetEmbedding A' B n k f) ∧
      AbsorbsEveryTargetFlipInside A B n k := by
  classical
  obtain ⟨bits,PT,hFull,hEmb⟩ :=
    exists_canonicalCausalOrbitFiniteTarget_with_prediary DA
  let B := canonicalCausalOrbitFiniteTarget DA bits
  let k := (canonicalCausalOrbitFiniteSupport DA bits).card
  let F := finiteCanonicalSignRootedFamily DA
  let maps : FiniteCanonicalFlipIndex A n → Nat → Nat :=
    fun i => canonicalCausalOrbitFiniteSourceMap DA bits i
  have hMaps :
      ∀ i : FiniteCanonicalFlipIndex A n,
        FiniteBoundedMeetEmbedding (F.graph i) B n k (maps i) :=
    hEmb
  have hCross : ∀ (i j : FiniteCanonicalFlipIndex A n)
      (s : FiniteTwoSplitIndex A n),
      F.node i s.val.val = F.node j s.val.val →
      (F.signature i).2 s ≠ (F.signature j).2 s →
      let W := finiteSelectedS2Witness DA s
      maps i s.val.val = maps j s.val.val ∧
      B.twoMeetLevel (maps i W.a) (maps i W.b)
          (maps j W.a) (maps j W.b) = maps i s.val.val := by
    intro i j s hShared hDiff
    exact canonicalCausalOrbitFiniteTarget_firstS2CrossMeet
      DA bits PT i j s hShared hDiff
  have hSeparate :
      ∀ (T : Ordered3Graph Nat) (FT : FiniteDiaryFlip B T k)
        (i j : FiniteCanonicalFlipIndex A n),
        i ≠ j →
        ∃ a b c : Fin n, a < b ∧ b < c ∧
          ¬ (T.edge (maps i a.val) (maps i b.val) (maps i c.val) ↔
             T.edge (maps j a.val) (maps j b.val) (maps j c.val)) :=
    finiteCanonical_explicit_maps_literal_separate_of_crossMeets
      DA maps hMaps hCross
  have hAbs : AbsorbsEveryTargetFlipInside A B n k := by
    apply absorbsEveryTargetFlipInside_of_explicit_literal_separation
      A B n k DA maps hMaps
    exact hSeparate
  have hAllFlips :
      ∀ A' : Ordered3Graph Nat,
        FiniteDiaryFlip A A' n →
        ∃ f : Nat → Nat,
          FiniteBoundedMeetEmbedding A' B n k f := by
    intro A' hFlip
    obtain ⟨i,hGraph⟩ :=
      finiteCanonicalSignRootedFamily_complete DA hFlip
    refine ⟨maps i, ?_⟩
    have hCopy : FiniteBoundedMeetEmbedding
        ((finiteCanonicalSignRootedFamily DA).graph i)
        B n k (maps i) := hMaps i
    rw [hGraph] at hCopy
    exact hCopy
  exact ⟨B,k,hFull,hAllFlips,hAbs⟩

/-- In particular every finite diary has an actual bounded
finite target absorbing the unflipped source under ALL of the
target's genuine finite flips. No abstract feedback or
positive-anchor covering hypothesis remains in the conclusion. -/
theorem exists_finiteDiary_universal_flip_absorber
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    ∃ (B : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock B k ∧
      AbsorbsEveryTargetFlipInside A B n k := by
  obtain ⟨B,k,hB,_hFirst,hSecond⟩ :=
    exists_finiteDiary_strong_both_flip_directions DA
  exact ⟨B,k,hB,hSecond⟩

end DiaryLeafPriority
end ThreeUniformDiaries
