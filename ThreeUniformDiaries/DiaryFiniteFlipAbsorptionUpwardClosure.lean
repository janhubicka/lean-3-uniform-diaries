import ThreeUniformDiaries.DiaryFinitePullbackProtectedEmbedding
import ThreeUniformDiaries.DiaryFiniteMeetEmbeddingComposition
import ThreeUniformDiaries.DiaryFiniteBoundedUniversality
import ThreeUniformDiaries.DiaryFiniteFlipTransitivity

/-!
# Strong finite flip absorption persists under protected target extensions

An arbitrary target flip does not preserve the original embedding
of B inside a larger diary C. Nevertheless, the **canonical induced
pullback** of that flip along B -> C is a genuine flip P of B,
and P still embeds with ALL numerical meets into the flipped C.

If B absorbs a fixed source A under every flip, it contains A in P.
Composing the two bounded meet embeddings yields A in the flipped C.

This is a new unconditional transport rule for the absorption
PREDICATE: it does not prove that any given A has an absorber.
In particular, protected joint embeddings can combine absorbers
for different sources without having to synchronise their
individual geometric flip constructions.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Composing bounded finite meet embeddings preserves both the
full induced/mixed-meet interface and the finite target image bound.
The intermediate bounded diary needs at least three marker positions. -/
theorem FiniteBoundedMeetEmbedding.comp
    {A B C : Ordered3Graph Nat} {n k l : Nat}
    {f g : Nat → Nat}
    (E : FiniteBoundedMeetEmbedding A B n k f)
    (D : FiniteBoundedMeetEmbedding B C k l g)
    (hk : 3 ≤ k) :
    FiniteBoundedMeetEmbedding A C n l (fun u => g (f u)) := by
  refine ⟨E.toMeetEmbedding.comp D.toMeetEmbedding hk
    (fun u _hu3 hu => E.image_bound u hu), ?_⟩
  intro u hu
  exact D.image_bound (f u) (E.image_bound u hu)

/-- The STRONG finite every-target-flip absorption property is
upward closed under bounded, induced, ALL-MEET preserving embeddings
of its absorbing target into a larger finite diary.

A flip of the larger target pulls back to a genuine flip of the
smaller absorber. First embed A there, then use the same protected
map to embed that pulled-back flip into the larger target flip. -/
theorem absorbsEveryTargetFlipInside_of_target_embedding
    {A B C : Ordered3Graph Nat} {n k l : Nat}
    {f : Nat → Nat}
    (DB : FiniteRoleDiaryBlock B k)
    (hAbs : AbsorbsEveryTargetFlipInside A B n k)
    (E : FiniteBoundedMeetEmbedding B C k l f) :
    AbsorbsEveryTargetFlipInside A C n l := by
  intro T FT
  let P := finiteDiaryPullbackGraph T k f
  have FP : FiniteDiaryFlip B P k :=
    finiteDiaryPullbackGraph_is_sourceFlip
      DB E.toMeetEmbedding E.image_bound FT
  obtain ⟨g,Eg⟩ := hAbs P FP
  have EP : FiniteBoundedMeetEmbedding P T k l f :=
    finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
      DB E FT
  exact ⟨fun u => f (g u),
    Eg.comp EP DB.prediary.frame.length_ge_three⟩

/-- Changing the BASELINE representative of a target flip class
does not change its strong BOUNDED absorption property.
The source A remains literally fixed. -/
theorem absorbsEveryTargetFlipInside_target_flip_iff
    {A B C : Ordered3Graph Nat} {n k : Nat}
    (F : FiniteDiaryFlip B C k) :
    AbsorbsEveryTargetFlipInside A B n k ↔
      AbsorbsEveryTargetFlipInside A C n k := by
  constructor
  · intro h T FT
    exact h T (F.trans FT)
  · intro h T FT
    exact h T (F.symm.trans FT)

/-- Two separately available finite flip-absorbing targets can
be combined into ONE finite diary absorbing both sources:
apply verified bounded finite-family joint embedding to the two
absorbers and transport absorption along each protected copy.
This theorem requires the two original absorbers as hypotheses. -/
theorem exists_joint_target_for_two_absorbing_sources
    (A A' : Ordered3Graph Nat) (n n' : Nat)
    (hFirst : ∃ (B : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock B k ∧
      AbsorbsEveryTargetFlipInside A B n k)
    (hSecond : ∃ (D : Ordered3Graph Nat) (m : Nat),
      FiniteRoleDiaryBlock D m ∧
      AbsorbsEveryTargetFlipInside A' D n' m) :
    ∃ (C : Ordered3Graph Nat) (l : Nat),
      FiniteRoleDiaryBlock C l ∧
      AbsorbsEveryTargetFlipInside A C n l ∧
      AbsorbsEveryTargetFlipInside A' C n' l := by
  obtain ⟨B,k,DB,hAbsB⟩ := hFirst
  obtain ⟨D,m,DD,hAbsD⟩ := hSecond
  let X : FiniteDiaryInput := ⟨B,k,DB⟩
  let Y : FiniteDiaryInput := ⟨D,m,DD⟩
  obtain ⟨C,l,DC,hCopies⟩ :=
    exists_finiteDiary_for_finiteFamily_bounded [X,Y]
  obtain ⟨f,Ef⟩ := hCopies X (by simp)
  obtain ⟨g,Eg⟩ := hCopies Y (by simp)
  refine ⟨C,l,DC,?_,?_⟩
  · exact absorbsEveryTargetFlipInside_of_target_embedding
      DB hAbsB Ef
  · exact absorbsEveryTargetFlipInside_of_target_embedding
      DD hAbsD Eg

end DiaryLeafPriority
end ThreeUniformDiaries
