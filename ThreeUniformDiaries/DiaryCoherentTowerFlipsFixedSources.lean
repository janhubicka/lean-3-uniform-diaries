import ThreeUniformDiaries.DiaryUniversalTowerAllHorizonFixedSourceCopies

/-!
# Track B: a FIXED finite source embeds coherently through every level
# of an ACTUAL coherent inverse system of finite target flips

The selected tower maps e_n : B_n -> B_(n+1) preserve the full
bounded diary, and their forward composites e_(i,k) obey a strict
semigroup law. We define a coherent tower-flip family as actual
genuine finite flips T_n of each B_n satisfying the LITERAL
canonical edge-table restriction
   Pullback(T_(n+1), e_n) = T_n.

This is a real inverse-system condition, not any arbitrary family
of unrelated target flips. The BASELINE T_n=B_n satisfies it
unconditionally, by the exact bounded induced embedding property.

For any such coherent family, any fixed finite source A already
strongly absorbed at one B_i has ONE base protected copy h:A->T_i
whose selected images e_(i,k) o h are bounded FULL-MEET copies
in T_(i+k), simultaneously for ALL k. The copies commute with
every tower transition and no further source-copy choices occur.

The source A remains FIXED. For a growing countable source
A_0 -> A_1 -> ..., no compatible base choices are supplied by
this theorem. The tower is an inverse system of FINITE FLIPS,
not an established countable RoleDiary colimit. The unrestricted
countable-source flip theorem remains open.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Actual compatible genuine finite flip at every stage of the
already verified strong finite absorber tower. The restriction
is the canonical induced FULL edge/nonedge pullback along the
selected bounded target embedding, not an arbitrary projection. -/
structure CoherentUniversalTowerFlips where
  graph : Nat → Ordered3Graph Nat
  genuine : ∀ n : Nat,
    FiniteDiaryFlip
      (universalStrongAbsorberTower n).graph (graph n)
      (universalStrongAbsorberTower n).bound
  restrict : ∀ n : Nat,
    finiteDiaryPullbackGraph (graph (n+1))
      (universalStrongAbsorberTower n).bound
      (universalStrongAbsorberTower_stepMap n) = graph n

/-- The baseline finite targets themselves form a genuine
coherent target-flip system under the selected transition maps.
This proves nonemptiness of the inverse flip system, but says
nothing about copying an arbitrary COUNTABLE source. -/
noncomputable def CoherentUniversalTowerFlips.baseline :
    CoherentUniversalTowerFlips := by
  refine {
    graph := fun n => (universalStrongAbsorberTower n).graph
    genuine := ?_
    restrict := ?_
  }
  · intro n
    exact FiniteDiaryFlip.refl
      (universalStrongAbsorberTower n).diary
  · intro n
    apply finiteDiaryPullbackGraph_unique
      (universalStrongAbsorberTower (n+1)).graph
      (universalStrongAbsorberTower n).bound
      (universalStrongAbsorberTower_stepMap n)
      (universalStrongAbsorberTower n).graph
      (universalStrongAbsorberTower n).diary.prediary.frame
    intro a b c hab hbc hcn
    exact ((universalStrongAbsorberTower_stepMap_spec n).toMeetEmbedding.edge_iff
      a b c hab hbc hcn).symm

namespace CoherentUniversalTowerFlips

/-- For any coherent family of ACTUAL finite target flips,
pulling the flip at level i+k back through the whole selected
composite gives EXACTLY the graph already specified at level i.
The proof inducts on k, using the verified full finite pullback
composition rather than silently identifying old target ranks. -/
theorem pullback_to_earlier
    (P : CoherentUniversalTowerFlips)
    (i k : Nat) :
    finiteDiaryPullbackGraph (P.graph (i+k))
      (universalStrongAbsorberTower i).bound
      (universalStrongAbsorberTower_forwardMap i k) =
      P.graph i := by
  induction k with
  | zero =>
      have hUnique :=
        finiteDiaryPullbackGraph_unique
          (P.graph i)
          (universalStrongAbsorberTower i).bound
          (fun u : Nat => u)
          (P.graph i)
          (P.genuine i).target_diary.prediary.frame
          (by
            intro a b c hab hbc hcn
            exact Iff.rfl)
      simpa only [Nat.add_zero,
        universalStrongAbsorberTower_forwardMap_zero] using hUnique
  | succ k ih =>
      have hPrev :
          finiteDiaryPullbackGraph (P.graph (i+(k+1)))
            (universalStrongAbsorberTower (i+k)).bound
            (universalStrongAbsorberTower_stepMap (i+k)) =
          P.graph (i+k) := by
        simpa only [Nat.add_succ] using P.restrict (i+k)
      calc
        finiteDiaryPullbackGraph (P.graph (i+(k+1)))
          (universalStrongAbsorberTower i).bound
          (universalStrongAbsorberTower_forwardMap i (k+1)) =
        finiteDiaryPullbackGraph
          (finiteDiaryPullbackGraph (P.graph (i+(k+1)))
            (universalStrongAbsorberTower (i+k)).bound
            (universalStrongAbsorberTower_stepMap (i+k)))
          (universalStrongAbsorberTower i).bound
          (universalStrongAbsorberTower_forwardMap i k) :=
            (universalStrongAbsorberTower_forwardPullback_succ_eq
              i k (P.graph (i+(k+1)))).symm
        _ = finiteDiaryPullbackGraph (P.graph (i+k))
              (universalStrongAbsorberTower i).bound
              (universalStrongAbsorberTower_forwardMap i k) := by
            rw [hPrev]
        _ = P.graph i := ih

/-- One protected FULL-MEET embedding of a fixed finite source
A into the base flipped target T_i transports simultaneously to
EVERY later flipped target T_(i+k) along the selected fixed tower
maps. This constructs one coherent infinite family of finite
source copies, conditional on the coherent target flip system P.

This does not assume a separate bounded image bound for each
source vertex, because the ambient target frame itself changes
along the tower. It does not construct any countable RoleDiary
target or embed an infinite source. -/
theorem exists_coherent_fixed_source_copies
    (P : CoherentUniversalTowerFlips)
    {A : Ordered3Graph Nat} {n i : Nat}
    (hAbs : AbsorbsEveryTargetFlipInside
      A (universalStrongAbsorberTower i).graph
      n (universalStrongAbsorberTower i).bound) :
    ∃ h : Nat → Nat,
      FiniteBoundedMeetEmbedding A (P.graph i)
        n (universalStrongAbsorberTower i).bound h ∧
      (∀ k : Nat,
        FiniteBoundedMeetEmbedding A (P.graph (i+k))
          n (universalStrongAbsorberTower (i+k)).bound
          (fun u => universalStrongAbsorberTower_forwardMap i k (h u))) := by
  classical
  obtain ⟨h,Eh⟩ := hAbs (P.graph i) (P.genuine i)
  refine ⟨h,Eh,?_⟩
  intro k
  have hSource :
      FiniteBoundedMeetEmbedding
        (finiteDiaryPullbackGraph (P.graph (i+k))
          (universalStrongAbsorberTower i).bound
          (universalStrongAbsorberTower_forwardMap i k))
        (P.graph (i+k))
        (universalStrongAbsorberTower i).bound
        (universalStrongAbsorberTower (i+k)).bound
        (universalStrongAbsorberTower_forwardMap i k) :=
    finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
      (universalStrongAbsorberTower i).diary
      (universalStrongAbsorberTower_forwardMap_spec i k)
      (P.genuine (i+k))
  rw [P.pullback_to_earlier i k] at hSource
  exact Eh.comp hSource
    (universalStrongAbsorberTower i).diary.prediary.frame.length_ge_three

/-- The maps in the infinite coherent fixed-source family commute
literally with all selected forward tower maps, independently
of the source A and of its chosen base copy h. -/
theorem fixed_source_maps_compatible
    (P : CoherentUniversalTowerFlips)
    (i j k : Nat) (h : Nat → Nat) :
    (fun u => universalStrongAbsorberTower_forwardMap i (j+k) (h u)) =
      (fun u =>
        universalStrongAbsorberTower_forwardMap (i+j) k
          (universalStrongAbsorberTower_forwardMap i j (h u))) := by
  exact universalStrongAbsorberTower_fixed_source_map_coherent i j k h

end CoherentUniversalTowerFlips

end DiaryLeafPriority
end ThreeUniformDiaries
