import ThreeUniformDiaries.DiaryFiniteCanonicalSourceFlipOrbit
import ThreeUniformDiaries.DiaryFinitePullbackProtectedEmbedding
import ThreeUniformDiaries.DiaryFiniteTargetFlipCodeCheck

/-!
# Exact multivalued canonical flip-absorption criterion

The earlier canonical-feedback permutation method fixes ONE embedding
for each source-flip code and demands injectivity under EVERY flip of
the target. That is a valid sufficient criterion, but may be stronger
than the original second finite flip property.

Here we prove an actual EQUIVALENCE, with no selected coherent family:
in a flip T of B, a bounded protected copy of the original A exists
iff one of the bounded protected copies P -> B of SOME genuine flip
P of A pulls back along the SAME map to precisely A.

The forward direction is the crucial converse: given A -> T, pull
the B-edge table back along that embedding, using the inverse
target flip T -> B. This produces a genuine source flip P of A
and a full bounded embedding P -> B. Pulling T back gives A exactly.

In particular the existential copy and source flip may depend on
T. This is a logically complete geometric covering criterion, not
an unproved permutation/injectivity hypothesis. The final theorem
also replaces the two abstract flip quantifiers by genuine finite
source/target Boolean code orbits. Embeddings remain supplied as
maps Nat -> Nat; their finite tabulation is a separate issue.

No existence of an absorbing B for arbitrary A is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- An exact multivalued geometric hitting criterion for strong
bounded absorption. Unlike the chosen-one-copy permutation
argument, this is a BICONDITIONAL for arbitrary given A,B.

Every flip of B must be hit by some embedded genuine source flip
P -> B whose literal pullback from that target flip is A.
Both the source flip and its selected embedding may depend on
the target flip. -/
theorem absorbsEveryTargetFlipInside_iff_all_source_flip_copies_hit
    {A B : Ordered3Graph Nat} {n k : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    AbsorbsEveryTargetFlipInside A B n k ↔
      ∀ (T : Ordered3Graph Nat) (FT : FiniteDiaryFlip B T k),
        ∃ (P : Ordered3Graph Nat),
          FiniteDiaryFlip A P n ∧
          ∃ f : Nat → Nat,
            FiniteBoundedMeetEmbedding P B n k f ∧
            finiteDiaryPullbackGraph T n f = A := by
  constructor
  · intro hAbs T FT
    obtain ⟨f,EA⟩ := hAbs T FT
    let P := finiteDiaryPullbackGraph B n f
    have FInv : FiniteDiaryFlip T B k := FT.symm
    have FP : FiniteDiaryFlip A P n :=
      finiteDiaryPullbackGraph_is_sourceFlip
        DA EA.toMeetEmbedding EA.image_bound FInv
    have EP : FiniteBoundedMeetEmbedding P B n k f :=
      finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
        DA EA FInv
    have hEq : finiteDiaryPullbackGraph T n f = A := by
      apply finiteDiaryPullbackGraph_unique
        T n f A DA.prediary.frame
      intro a b c hab hbc hcn
      exact (EA.toMeetEmbedding.edge_iff a b c hab hbc hcn).symm
    exact ⟨P,FP,f,EP,hEq⟩
  · intro hHits T FT
    obtain ⟨P,FP,f,EP,hPull⟩ := hHits T FT
    have ETarget : FiniteBoundedMeetEmbedding
        (finiteDiaryPullbackGraph T n f) T n k f :=
      finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
        FP.target_diary EP FT
    exact ⟨f,by simpa only [hPull] using ETarget⟩

/-- The complete finite-code version of the preceding criterion:
for each actual finite target flip code, SOME actual canonical source
flip code and SOME bounded protected map must pull back to A.

Both quantified flip orbits are finite. This criterion is necessary
AND sufficient for the second finite flip property for this fixed
pair of source and target diaries, unlike feedback injectivity.

It does not say the set of bounded maps has already been explicitly
enumerated; no free Boolean controls are introduced. -/
theorem absorbsEveryTargetFlipInside_iff_finite_multivalued_flip_codes
    {A B : Ordered3Graph Nat} {n k : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    AbsorbsEveryTargetFlipInside A B n k ↔
      ∀ tcode : FiniteDiaryEdgeCode k,
        tcode ∈ finiteSourceFlipCodes B k →
        ∃ scode : FiniteDiaryEdgeCode n,
          scode ∈ finiteCanonicalSourceFlipCodes A n ∧
          ∃ f : Nat → Nat,
            FiniteBoundedMeetEmbedding
              (finiteDiaryCodeGraph n scode) B n k f ∧
            finiteDiaryPullbackGraph
              (finiteDiaryCodeGraph k tcode) n f = A := by
  constructor
  · intro hAbs tcode ht
    let T := finiteDiaryCodeGraph k tcode
    have FT : FiniteDiaryFlip B T k :=
      (mem_finiteSourceFlipCodes_iff B k tcode).mp ht
    obtain ⟨P,FP,f,EP,hPull⟩ :=
      (absorbsEveryTargetFlipInside_iff_all_source_flip_copies_hit
        DA).mp hAbs T FT
    obtain ⟨scode,hc,hDecoded⟩ :=
      finiteCanonicalSourceFlipCodes_complete FP
    refine ⟨scode,hc,f,?_,?_⟩
    · simpa only [hDecoded] using EP
    · exact hPull
  · intro hCodes
    apply (absorbsEveryTargetFlipInside_iff_all_source_flip_copies_hit
      DA).mpr
    intro T FT
    let tcode := finiteDiaryEdgeCode T k
    have hReconstruct :
        finiteDiaryCodeGraph k tcode = T :=
      finiteDiaryCodeGraph_reconstruct T k
        FT.target_diary.prediary.frame
    have ht : tcode ∈ finiteSourceFlipCodes B k :=
      (mem_finiteSourceFlipCodes_iff B k tcode).mpr (by
        rw [hReconstruct]
        exact FT)
    obtain ⟨scode,hc,f,EP,hPull⟩ := hCodes tcode ht
    have hRaw : scode ∈ finiteSourceFlipCodes A n :=
      ((mem_finiteCanonicalSourceFlipCodes_iff A n scode).mp hc).1
    have FP : FiniteDiaryFlip A
        (finiteDiaryCodeGraph n scode) n :=
      (mem_finiteSourceFlipCodes_iff A n scode).mp hRaw
    refine ⟨finiteDiaryCodeGraph n scode,FP,f,EP,?_⟩
    simpa only [hReconstruct] using hPull

end DiaryLeafPriority
end ThreeUniformDiaries
