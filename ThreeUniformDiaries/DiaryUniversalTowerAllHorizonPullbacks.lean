import ThreeUniformDiaries.DiaryUniversalTowerFlipRestriction

/-!
# Track B: a coherent selected tower map across EVERY finite horizon

The merged finite strong-absorber tower gives genuine full finite diaries
B_i. The preceding Track B module picks a fixed bounded, induced,
all-numerical-meet-preserving transition map e_i : B_i -> B_(i+1).

Compose these ACTUAL fixed maps recursively:
  e_(i,0) = identity on B_i;
  e_(i,k+1) = e_(i+k) o e_(i,k).

All e_(i,k) are bounded protected embeddings. For ANY genuine finite
flip of B_(i+k), its induced pullback along e_(i,k) is a genuine finite
flip of B_i. Pulling back an additional step first is LITERALLY EQUAL
to pulling back directly through the longer composite, including every
edge and nonedge of the finite source table.

This goes beyond separate existential earlier-to-later embeddings:
the maps are selected once and compose definitionally.

The result still does not build a countable diary colimit and does
not choose coherent embeddings of a prescribed countable SOURCE
into target flips. No countable-source flip absorption is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The exact selected forward map from tower level i to level i+k,
obtained by composing the same fixed transition maps at all steps. -/
noncomputable def universalStrongAbsorberTower_forwardMap
    (i k : Nat) : Nat → Nat :=
  Nat.rec
    (fun u : Nat => u)
    (fun j f u =>
      universalStrongAbsorberTower_stepMap (i+j) (f u))
    k

theorem universalStrongAbsorberTower_forwardMap_zero
    (i : Nat) :
    universalStrongAbsorberTower_forwardMap i 0 =
      (fun u : Nat => u) := rfl

theorem universalStrongAbsorberTower_forwardMap_succ
    (i k : Nat) :
    universalStrongAbsorberTower_forwardMap i (k+1) =
      (fun u =>
        universalStrongAbsorberTower_stepMap (i+k)
          (universalStrongAbsorberTower_forwardMap i k u)) := rfl

/-- Every composed selected tower map is a fully bounded induced
embedding preserving ALL numerical singleton and pair meets,
without independently selecting a new witness at a later horizon. -/
theorem universalStrongAbsorberTower_forwardMap_spec
    (i k : Nat) :
    FiniteBoundedMeetEmbedding
      (universalStrongAbsorberTower i).graph
      (universalStrongAbsorberTower (i+k)).graph
      (universalStrongAbsorberTower i).bound
      (universalStrongAbsorberTower (i+k)).bound
      (universalStrongAbsorberTower_forwardMap i k) := by
  induction k with
  | zero =>
      simpa only [Nat.add_zero,
        universalStrongAbsorberTower_forwardMap_zero] using
        (universalStrongAbsorberTower i).boundedIdentity
  | succ k ih =>
      have hStep :
          FiniteBoundedMeetEmbedding
            (universalStrongAbsorberTower (i+k)).graph
            (universalStrongAbsorberTower (i+(k+1))).graph
            (universalStrongAbsorberTower (i+k)).bound
            (universalStrongAbsorberTower (i+(k+1))).bound
            (universalStrongAbsorberTower_stepMap (i+k)) := by
        simpa only [Nat.add_succ, Nat.add_assoc] using
          universalStrongAbsorberTower_stepMap_spec (i+k)
      have hComp := ih.comp hStep
        (universalStrongAbsorberTower (i+k)).diary.prediary.frame.length_ge_three
      simpa only [universalStrongAbsorberTower_forwardMap_succ] using hComp

/-- Pulling back an actual finite flip of ANY later tower target
along the FIXED selected composite produces a genuine finite flip
of the earliest target. This is not an assertion about an arbitrary
target graph, nor an independent source-embedding choice. -/
theorem universalStrongAbsorberTower_forwardPullback_is_flip
    (i k : Nat) (T : Ordered3Graph Nat)
    (FT : FiniteDiaryFlip
      (universalStrongAbsorberTower (i+k)).graph T
      (universalStrongAbsorberTower (i+k)).bound) :
    FiniteDiaryFlip
      (universalStrongAbsorberTower i).graph
      (finiteDiaryPullbackGraph T
        (universalStrongAbsorberTower i).bound
        (universalStrongAbsorberTower_forwardMap i k))
      (universalStrongAbsorberTower i).bound := by
  exact finiteDiaryPullbackGraph_is_sourceFlip
    (universalStrongAbsorberTower i).diary
    (universalStrongAbsorberTower_forwardMap_spec i k).toMeetEmbedding
    (universalStrongAbsorberTower_forwardMap_spec i k).image_bound
    FT

/-- The entire finite edge-and-nonedge pullback is coherent when
one moves from an arbitrary horizon k to k+1.
The equality holds for any raw ternary target graph T; the
next theorem adds genuine target flip hypotheses. -/
theorem universalStrongAbsorberTower_forwardPullback_succ_eq
    (i k : Nat) (T : Ordered3Graph Nat) :
    finiteDiaryPullbackGraph
      (finiteDiaryPullbackGraph T
        (universalStrongAbsorberTower (i+k)).bound
        (universalStrongAbsorberTower_stepMap (i+k)))
      (universalStrongAbsorberTower i).bound
      (universalStrongAbsorberTower_forwardMap i k) =
    finiteDiaryPullbackGraph T
      (universalStrongAbsorberTower i).bound
      (universalStrongAbsorberTower_forwardMap i (k+1)) := by
  have h := finiteDiaryPullbackGraph_comp_of_bounded
    (universalStrongAbsorberTower_forwardMap_spec i k)
    (universalStrongAbsorberTower_stepMap (i+k))
  simpa only [universalStrongAbsorberTower_forwardMap_succ] using h

/-- Combining the genuine flip status and the strict literal
pullback identity: ANY actual finite flip at tower horizon i+k+1
restricts coherently to B_i, and taking one intermediate step
does not change the source flip's finite edge/nonedge table. -/
theorem universalStrongAbsorberTower_forwardPullback_succ_flip
    (i k : Nat) (T : Ordered3Graph Nat)
    (FT : FiniteDiaryFlip
      (universalStrongAbsorberTower (i+(k+1))).graph T
      (universalStrongAbsorberTower (i+(k+1))).bound) :
    FiniteDiaryFlip
      (universalStrongAbsorberTower i).graph
      (finiteDiaryPullbackGraph T
        (universalStrongAbsorberTower i).bound
        (universalStrongAbsorberTower_forwardMap i (k+1)))
      (universalStrongAbsorberTower i).bound ∧
    finiteDiaryPullbackGraph
      (finiteDiaryPullbackGraph T
        (universalStrongAbsorberTower (i+k)).bound
        (universalStrongAbsorberTower_stepMap (i+k)))
      (universalStrongAbsorberTower i).bound
      (universalStrongAbsorberTower_forwardMap i k) =
    finiteDiaryPullbackGraph T
      (universalStrongAbsorberTower i).bound
      (universalStrongAbsorberTower_forwardMap i (k+1)) := by
  exact ⟨universalStrongAbsorberTower_forwardPullback_is_flip
    i (k+1) T FT,
    universalStrongAbsorberTower_forwardPullback_succ_eq i k T⟩

end DiaryLeafPriority
end ThreeUniformDiaries
