import ThreeUniformDiaries.DiaryCofinalBoundedCountableFusion

/-!
# Track A audit: cofinal bounded next leaves are exactly persistent successors

For one genuine source leaf, the cofinal bounded-image hypothesis needed by
the conditional countable-diary fusion theorem is EQUIVALENT to existence
of one finitely persistent compatible successor stage.

The forward implication uses the already verified finite-cover/finite-choice
lemma, followed by full support determinacy from selected leaf images.
Conversely, persistence of a single successor fixes its new-leaf image:
every later horizon has a compatible reserved witness with that SAME image.

This is an exact diagnostic of the missing no-escape obligation. It does NOT
prove the hypothesis for generic leaf ranges, or establish unconditional
countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For a genuine next source leaf m, uniform bounded next-image
realization at cofinally many finite horizons is exactly the ability
to choose one genuine finitely persistent successor compatible with
the old supported stage. No persistent old-stage premise is needed
for this pointwise equivalence. -/
theorem cofinalBoundedNextLeafImages_iff_persistent_successor
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m) :
    HasCofinalBoundedNextLeafImages H K F f m ↔
      ∃ g : Nat → Nat,
        PersistentReservedDiaryStage H K F (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g := by
  constructor
  · intro hBound
    exact exists_persistent_reserved_successor_of_finite_cover hm
      (finiteHorizonNextLeafCover_of_cofinal_bounded_images
        H K F f m hBound)
  · rintro ⟨g, P, hOld⟩
    refine ⟨g m, ?_⟩
    intro N
    obtain ⟨gN, QN, hNext⟩ := P.2 N
    have hmNext : m ∈ countableDiaryFiniteSupport H (m + 1) := by
      exact mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1)) m
        ((mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
          ⟨hm.1, by omega, hm⟩)
    refine ⟨N, le_rfl, gN, QN, ?_, ?_⟩
    · intro u hu
      have huNext : u ∈ countableDiaryFiniteSupport H (m + 1) :=
        countableDiaryFiniteSupport_mono H m (m + 1)
          (by omega) hu
      exact (hNext u huNext).trans (hOld u hu)
    · exact le_of_eq (hNext m hmNext)

/-- The UNREFINED geometric boundedness obligation at every persistent
finite stage is equivalent to an actual one-step persistent extension
property. This is the precise missing no-escape statement; neither
side follows from independent nonempty finite horizons alone. -/
theorem allPersistentStages_cofinalBounded_iff_extend
    {H K : Ordered3Graph Nat} (F : Nat → Nat) :
    (∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        PersistentReservedDiaryStage H K F m f →
        HasCofinalBoundedNextLeafImages H K F f m) ↔
    (∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        PersistentReservedDiaryStage H K F m f →
        ∃ g : Nat → Nat,
          PersistentReservedDiaryStage H K F (m + 1) g ∧
          CofinalDiaryStageCompatible H m f g) := by
  constructor
  · intro h m hm f Pf
    exact (cofinalBoundedNextLeafImages_iff_persistent_successor hm).mp
      (h m hm f Pf)
  · intro h m hm f Pf
    exact (cofinalBoundedNextLeafImages_iff_persistent_successor hm).mpr
      (h m hm f Pf)

end DiaryLeafPriority
end ThreeUniformDiaries
