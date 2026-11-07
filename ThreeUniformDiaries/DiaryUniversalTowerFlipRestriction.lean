import ThreeUniformDiaries.DiaryUniversalFiniteStrongAbsorberTower
import ThreeUniformDiaries.DiaryFiniteFlipPullbackComposition

/-!
# Track B: the finite strong absorber tower has coherent flip restrictions

The verified finite strong absorber tower provides, at each successor
stage n, an actual bounded all-meet embedding of finite full diaries
  B_n -> B_(n+1).
We SELECT the already existent transition map once and for all by
classical choice, instead of re-choosing unrelated maps in each later
proof.

Every actual flip T of B_(n+1) has a genuine canonical pulled-back
flip of B_n along this selected transition map. More strongly, every
actual flip of B_(n+2) restricts to the SAME exact induced source flip
of B_n whether we first pull back to B_(n+1) or directly along the
two-step composite.

This is literal coherence of the TARGET-FLIP DATA in the tower.
It does NOT select source diary copies inside target flips coherently,
construct a countable RoleDiary carrier, or prove unrestricted
countable-source flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Fix a concrete bounded protected transition map at each
stage of the strong finite absorber tower. -/
noncomputable def universalStrongAbsorberTower_stepMap
    (n : Nat) : Nat → Nat :=
  Classical.choose (universalStrongAbsorberTower_next_embedding n)

/-- The chosen transition really is a bounded exact-meet embedding
on its ENTIRE finite source support, not an arbitrary map on the
artificial Nat tail. -/
theorem universalStrongAbsorberTower_stepMap_spec
    (n : Nat) :
    FiniteBoundedMeetEmbedding
      (universalStrongAbsorberTower n).graph
      (universalStrongAbsorberTower (n+1)).graph
      (universalStrongAbsorberTower n).bound
      (universalStrongAbsorberTower (n+1)).bound
      (universalStrongAbsorberTower_stepMap n) := by
  exact Classical.choose_spec
    (universalStrongAbsorberTower_next_embedding n)

/-- Every genuine finite flip of the next tower target pulls
back to a genuine finite flip of the present target. The
pullback is literal and unique as an induced full edge table. -/
theorem universalStrongAbsorberTower_step_pullback_is_flip
    (n : Nat)
    (T : Ordered3Graph Nat)
    (FT : FiniteDiaryFlip
      (universalStrongAbsorberTower (n+1)).graph T
      (universalStrongAbsorberTower (n+1)).bound) :
    FiniteDiaryFlip
      (universalStrongAbsorberTower n).graph
      (finiteDiaryPullbackGraph T
        (universalStrongAbsorberTower n).bound
        (universalStrongAbsorberTower_stepMap n))
      (universalStrongAbsorberTower n).bound := by
  exact finiteDiaryPullbackGraph_is_sourceFlip
    (universalStrongAbsorberTower n).diary
    (universalStrongAbsorberTower_stepMap_spec n).toMeetEmbedding
    (universalStrongAbsorberTower_stepMap_spec n).image_bound FT

/-- Exact TWO-STEP pullback coherence for REAL tower target flips.
Both intermediate and directly pulled-back graphs are genuine
finite flips of their original full targets, and the two edge
tables on the earliest tower frame are LITERALLY equal.

The statement is a concrete application of the verified general
finite pullback-composition theorem, not a new assertion that
unrelated embeddings of source finite supports are compatible. -/
theorem universalStrongAbsorberTower_two_step_flip_coherent
    (n : Nat)
    (T : Ordered3Graph Nat)
    (FT : FiniteDiaryFlip
      (universalStrongAbsorberTower (n+2)).graph T
      (universalStrongAbsorberTower (n+2)).bound) :
    FiniteDiaryFlip
      (universalStrongAbsorberTower (n+1)).graph
      (finiteDiaryPullbackGraph T
        (universalStrongAbsorberTower (n+1)).bound
        (universalStrongAbsorberTower_stepMap (n+1)))
      (universalStrongAbsorberTower (n+1)).bound ∧
    FiniteDiaryFlip
      (universalStrongAbsorberTower n).graph
      (finiteDiaryPullbackGraph T
        (universalStrongAbsorberTower n).bound
        (fun u =>
          universalStrongAbsorberTower_stepMap (n+1)
            (universalStrongAbsorberTower_stepMap n u)))
      (universalStrongAbsorberTower n).bound ∧
    finiteDiaryPullbackGraph
      (finiteDiaryPullbackGraph T
        (universalStrongAbsorberTower (n+1)).bound
        (universalStrongAbsorberTower_stepMap (n+1)))
      (universalStrongAbsorberTower n).bound
      (universalStrongAbsorberTower_stepMap n) =
    finiteDiaryPullbackGraph T
      (universalStrongAbsorberTower n).bound
      (fun u =>
        universalStrongAbsorberTower_stepMap (n+1)
          (universalStrongAbsorberTower_stepMap n u)) := by
  have h := finiteDiaryPullbackGraph_comp_sourceFlip
    (universalStrongAbsorberTower n).diary
    (universalStrongAbsorberTower (n+1)).diary
    (universalStrongAbsorberTower_stepMap_spec n)
    (universalStrongAbsorberTower_stepMap_spec (n+1))
    FT
  simpa only [Nat.add_assoc] using h

end DiaryLeafPriority
end ThreeUniformDiaries
