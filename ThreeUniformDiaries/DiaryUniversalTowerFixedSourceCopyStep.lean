import ThreeUniformDiaries.DiaryUniversalTowerAllHorizonPullbacks
import ThreeUniformDiaries.DiaryFinitePullbackProtectedEmbedding

/-!
# Track B: compatible copies of a FIXED finite source across a target flip step

The selected finite strong-absorber tower now has exact bounded maps
B_i -> B_(i+k), and genuine target flips pull back along those
composites with literal edge/nonedge table coherence.

We fix a finite source A already strongly absorbed at ONE base
tower stage B_i. For any actual target flip T at stage B_(i+k+1):
  1. Pull T back along the selected last step to a genuine
     finite flip Tprev of B_(i+k).
  2. Pull Tprev back to a genuine flip U of B_i.
  3. Choose ONE bounded full-meet copy A -> U using strong absorption.
  4. Compose first into Tprev and then into T.

This constructs compatible embeddings of the SAME finite source
A into the two consecutive target flips, with the later copy
literally equal to the last tower transition applied to the
earlier copy.

This is genuinely stronger than independent absorption witnesses
at two target stages, but remains a ONE-STEP compatibility result
for ONE FIXED finite source. It does NOT select copies of the
different growing source prefixes A_n compatibly, construct a
countable diary colimit, or solve countable-source flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any finite source A absorbed at base tower stage i has
compatible FULL-MEET copies at two consecutive later target
flip levels, for every genuine target flip T of the later level.

The target flip at the preceding level is its canonical induced
pullback, not an independently chosen flip. The same source
copy is transported by the selected last tower embedding. -/
theorem exists_compatible_fixed_source_copies_across_tower_step
    {A : Ordered3Graph Nat} {n i k : Nat}
    (hAbs : AbsorbsEveryTargetFlipInside
      A (universalStrongAbsorberTower i).graph
      n (universalStrongAbsorberTower i).bound)
    (T : Ordered3Graph Nat)
    (FT : FiniteDiaryFlip
      (universalStrongAbsorberTower ((i+k)+1)).graph T
      (universalStrongAbsorberTower ((i+k)+1)).bound) :
    ∃ (f g : Nat → Nat),
      FiniteBoundedMeetEmbedding
        A
        (finiteDiaryPullbackGraph T
          (universalStrongAbsorberTower (i+k)).bound
          (universalStrongAbsorberTower_stepMap (i+k)))
        n (universalStrongAbsorberTower (i+k)).bound f ∧
      FiniteBoundedMeetEmbedding
        A T n
        (universalStrongAbsorberTower ((i+k)+1)).bound g ∧
      (∀ u : Nat, u < n →
        g u =
          universalStrongAbsorberTower_stepMap (i+k) (f u)) := by
  classical
  let Tprev : Ordered3Graph Nat :=
    finiteDiaryPullbackGraph T
      (universalStrongAbsorberTower (i+k)).bound
      (universalStrongAbsorberTower_stepMap (i+k))
  have hPrev : FiniteDiaryFlip
      (universalStrongAbsorberTower (i+k)).graph
      Tprev (universalStrongAbsorberTower (i+k)).bound :=
    universalStrongAbsorberTower_step_pullback_is_flip (i+k) T FT
  let U : Ordered3Graph Nat :=
    finiteDiaryPullbackGraph Tprev
      (universalStrongAbsorberTower i).bound
      (universalStrongAbsorberTower_forwardMap i k)
  have hBase : FiniteDiaryFlip
      (universalStrongAbsorberTower i).graph U
      (universalStrongAbsorberTower i).bound :=
    universalStrongAbsorberTower_forwardPullback_is_flip
      i k Tprev hPrev
  obtain ⟨h,Eh⟩ := hAbs U hBase
  have EP : FiniteBoundedMeetEmbedding
      U Tprev
      (universalStrongAbsorberTower i).bound
      (universalStrongAbsorberTower (i+k)).bound
      (universalStrongAbsorberTower_forwardMap i k) :=
    finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
      (universalStrongAbsorberTower i).diary
      (universalStrongAbsorberTower_forwardMap_spec i k)
      hPrev
  have Eprev : FiniteBoundedMeetEmbedding
      A Tprev n (universalStrongAbsorberTower (i+k)).bound
      (fun u => universalStrongAbsorberTower_forwardMap i k (h u)) :=
    Eh.comp EP
      (universalStrongAbsorberTower i).diary.prediary.frame.length_ge_three
  have Etop : FiniteBoundedMeetEmbedding
      Tprev T
      (universalStrongAbsorberTower (i+k)).bound
      (universalStrongAbsorberTower ((i+k)+1)).bound
      (universalStrongAbsorberTower_stepMap (i+k)) :=
    finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
      (universalStrongAbsorberTower (i+k)).diary
      (universalStrongAbsorberTower_stepMap_spec (i+k)) FT
  refine ⟨(fun u => universalStrongAbsorberTower_forwardMap i k (h u)),
    (fun u => universalStrongAbsorberTower_stepMap (i+k)
      (universalStrongAbsorberTower_forwardMap i k (h u))),
    Eprev, ?_, ?_⟩
  · exact Eprev.comp Etop
      (universalStrongAbsorberTower (i+k)).diary.prediary.frame.length_ge_three
  · intro u hu
    rfl

/-- Specialization to the genuine FULL finite source diaries
of exact source size i+4. The tower stage i+1 strongly absorbs
every such source, so the preceding compatible-copy result is
unconditional for that finite source (modulo the supplied actual
target flip at the later tower stage). -/
theorem exists_compatible_size_source_copies_across_tower_step
    {A : Ordered3Graph Nat} (i k : Nat)
    (DA : FiniteRoleDiaryBlock A (i+4))
    (T : Ordered3Graph Nat)
    (FT : FiniteDiaryFlip
      (universalStrongAbsorberTower (((i+1)+k)+1)).graph T
      (universalStrongAbsorberTower (((i+1)+k)+1)).bound) :
    ∃ (f g : Nat → Nat),
      FiniteBoundedMeetEmbedding A
        (finiteDiaryPullbackGraph T
          (universalStrongAbsorberTower ((i+1)+k)).bound
          (universalStrongAbsorberTower_stepMap ((i+1)+k)))
        (i+4) (universalStrongAbsorberTower ((i+1)+k)).bound f ∧
      FiniteBoundedMeetEmbedding A T (i+4)
        (universalStrongAbsorberTower (((i+1)+k)+1)).bound g ∧
      (∀ u : Nat, u < i+4 →
        g u = universalStrongAbsorberTower_stepMap ((i+1)+k) (f u)) := by
  exact exists_compatible_fixed_source_copies_across_tower_step
    (universalStrongAbsorberTower_next_absorbs i A DA)
    T FT

end DiaryLeafPriority
end ThreeUniformDiaries
