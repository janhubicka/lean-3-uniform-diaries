import ThreeUniformDiaries.DiaryCofinalBoundedCountableFusion
import ThreeUniformDiaries.DiaryUpperBoundCofinalPersistentFiniteCovers

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


namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- After EVERY ordinary colour-stabilising selfcopy w₀ there is a
further induced selfcopy i for which EVERY finitely persistent leaf
stage has a compatible, finitely persistent next-leaf successor.
This is a geometric strengthening of the existential certified
fusion hypothesis: it does NOT follow from finite genericity. -/
def HasCofinalPersistentSuccessorRefinement
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H) (F : UnorderedEmbedding U H) : Prop :=
  ∀ w₀ : UnorderedEmbedding U U,
    ∃ i : UnorderedEmbedding U U,
      ∀ m : Nat, IsLeaf H m →
        ∀ f : Nat → Nat,
          PersistentReservedDiaryStage H H
            (fun t => F (w₀ (i t))) m f →
          ∃ g : Nat → Nat,
            PersistentReservedDiaryStage H H
              (fun t => F (w₀ (i t))) (m + 1) g ∧
            CofinalDiaryStageCompatible H m f g

/-- The exact, UNPROVED Track A cofinal finite-cover criterion is
equivalent to persistent next-leaf extension AFTER one refinement
i of each originally chosen ordinary selfcopy w₀.

This equivalence does not assert the existence of such a refinement.
It does not equate the sufficient criterion with the eventual Ramsey
conclusion, which might admit a weaker tailored Safe subsystem. -/
theorem cofinalPersistentSuccessorRefinement_iff_finiteCovers
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H) (F : UnorderedEmbedding U H) :
    HasCofinalPersistentSuccessorRefinement D F ↔
      HasCofinalPersistentFiniteNextLeafCovers D F := by
  constructor
  · intro hSuccessor w₀
    obtain ⟨i, hi⟩ := hSuccessor w₀
    refine ⟨i, ?_⟩
    intro m hm f hf
    have hSucc := hi m hm f hf
    have hCofinal :
        HasCofinalBoundedNextLeafImages H H
          (fun t => F (w₀ (i t))) f m :=
      (cofinalBoundedNextLeafImages_iff_persistent_successor hm).mpr hSucc
    exact finiteHorizonNextLeafCover_of_cofinal_bounded_images
      H H (fun t => F (w₀ (i t))) f m hCofinal
  · intro hCovers w₀
    obtain ⟨i, hi⟩ := hCovers w₀
    refine ⟨i, ?_⟩
    intro m hm f hf
    exact exists_persistent_reserved_successor_of_finite_cover hm
      (hi m hm f hf)

/-- The verified sharp LABELLED diary upper under the concrete
relative persistent-next-leaf extension criterion. The criterion
is NOT shown to hold in generic prescribed leaf copies here. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_of_cofinalPersistentSuccessors
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsDiaryLeafLabelledCopy A H v} → κ)
    (hExtend : HasCofinalPersistentSuccessorRefinement D F) :
    ∃ (h : Ordered3Graph.Embedding H H)
      (palette : List κ),
        palette.length =
          (∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card) *
          Fintype.card
            (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        h.TypeRespecting ∧
        (h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2) ∧
        ∀ v : Fin a → Nat,
          IsDiaryLeafLabelledCopy A H v →
          ∃ hOutput :
              IsDiaryLeafLabelledCopy A H (fun j => h (v j)),
            χ ⟨(fun j => h (v j)), hOutput⟩ ∈ palette := by
  exact actualFiniteAuxRamsey_allDiaryLeaf_upper_of_cofinal_finite_covers
    U H D F hLeaf hUniversal A χ
    ((cofinalPersistentSuccessorRefinement_iff_finiteCovers D F).mp hExtend)

end ATRFiniteDecoder
end ThreeUniformDiaries
