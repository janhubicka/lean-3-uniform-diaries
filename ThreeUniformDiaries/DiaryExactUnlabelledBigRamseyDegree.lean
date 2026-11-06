import ThreeUniformDiaries.DiaryLowerCanonicalUnmarkedColour
import ThreeUniformDiaries.DiarySharpUpperNoGenericParameter
import ThreeUniformDiaries.DiaryExistenceCountableLeafOrderEquiv
import ThreeUniformDiaries.DiaryGenericExistenceByPairCode

/-!
# Track C: exact big Ramsey degree of UNLABELLED finite 3-hypergraph copies

The verified labelled degree has a factor |Aut(A)| because its
colours distinguish *labelled induced embeddings*. The independently
verified sharp upper bound on unlabelled vertex-set copies has NO
such factor. Dividing the labelled lower degree by |Aut(A)| does
not prove a matching unlabelled lower bound, because colours could
collapse differently inside particular selfcopies.

Here we instead use the genuine canonical UNMARKED full diary
colouring and its geometric unavoidability (prior Track C PR).
The unmarked colour is independent of the labelled copy chosen
as witness, and every true unmarked finite diary shape persists
inside every induced selfcopy. This supplies the precise lower
obstruction. The upper bound is the already verified unlabelled
finite ATR result, with its list palette converted to a finite
set of distinct colours.

The resulting degree counts every increasing ordered presentation
of the underlying unordered A but does NOT multiply by |Aut(A)|.
No diary countable-source unavoidability or diary Ramsey is used.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph
open DiaryLeafPriority

/-- The literal big Ramsey bound for UNLABELLED finite copies:
colourings act on finite vertex sets, and the conclusion ranges
only over images of ACTUAL induced labelled A-embeddings. Thus
there is no implicit multiplicity from different labellings of
the same finite subset. -/
def IsUnlabelledBigRamseyBound
    (U : Ordered3Graph Nat) {a : Nat} (A : EnumNode a)
    (t : Nat) : Prop :=
  ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (χ : Finset Nat → κ),
    ∃ (w : UnorderedEmbedding U U) (palette : Finset κ),
      palette.card ≤ t ∧
      ∀ v : GenuineFiniteEmbeddings A U,
        χ ((Finset.univ : Finset (Fin a)).image
          (fun i => w (v.val i))) ∈ palette

/-- The already proved unlabelled upper bound, with the
genuine full-diary count and NO automorphism multiplier. -/
theorem exactUnmarkedDiaryCount_is_unlabelledBigRamseyBound
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a) :
    IsUnlabelledBigRamseyBound U A
      (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) := by
  classical
  intro κ _ _ χ
  obtain ⟨w, palette, hLength, hCover⟩ :=
    actualFiniteAuxRamsey_sharp_unlabelled_upper_noGeneric
      U hUniversal A χ
  refine ⟨w, palette.toFinset, ?_, ?_⟩
  · calc
      palette.toFinset.card ≤ palette.length :=
        List.toFinset_card_le palette
      _ = (∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card) :=
        hLength
  · intro v
    simpa using (hCover v.val v.property)

/-- Eliminate the auxiliary full-diary leaf model from the
UNMARKED lower-colouring construction using the checked countable
diary existence theorem, and instantiate the finite unavoidability
argument with the concrete enumerated generic witness. -/
theorem exists_unavoidableUnmarkedDiaryColour_in_universal
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a) :
    ∃ χ : GenuineUnlabelledCopies A U →
        ↑(allGenuineUnmarkedDiarySources A),
      ∀ (w : UnorderedEmbedding U U)
        (d : ↑(allGenuineUnmarkedDiarySources A)),
        ∃ v : GenuineFiniteEmbeddings A U,
          χ ⟨(Finset.univ : Finset (Fin a)).image
                (v.postcompose w).val,
             ⟨v.postcompose w, rfl⟩⟩ = d := by
  classical
  obtain ⟨K, e, DK, hOrder, hEdge⟩ :=
    exists_countable_diary_order_equiv_leaf_reduct U
  let F : UnorderedEmbedding U K := {
    toFun := fun x => (e x).val
    injective := by
      intro x y hxy
      apply e.injective
      apply Subtype.ext
      exact hxy
    edge_iff := by
      intro x y z hxy hyz
      have hxyK : (e x).val < (e y).val :=
        (hOrder x y).mp hxy
      have hyzK : (e y).val < (e z).val :=
        (hOrder y z).mp hyz
      calc
        U.unorderedEdge x y z ↔ U.edge x y z :=
          U.unorderedEdge_iff_of_lt x y z hxy hyz
        _ ↔ K.edge (e x).val (e y).val (e z).val :=
          (hEdge x y z hxy hyz).symm
        _ ↔ K.unorderedEdge (e x).val (e y).val (e z).val :=
          (K.unorderedEdge_iff_of_lt
            (e x).val (e y).val (e z).val hxyK hyzK).symm
  }
  have hFLeaf : ∀ u : Nat, IsLeaf K (F u) :=
    fun u => (e u).property
  refine ⟨canonicalUnmarkedDiaryColour DK F hFLeaf A, ?_⟩
  exact canonicalUnmarkedDiaryColour_unavoidable
    canonicalGenericEnumerated3Graph U K hUniversal
    DK F hFLeaf A

/-- The genuine unmarked canonical diary colouring supplies
the missing LOWER obstruction: for any claimed unlabelled
big Ramsey palette t, every single true unmarked diary source
forces a distinct colour inside every induced selfcopy. Use
Option to obtain a nonempty finite colour type even at a=0. -/
theorem unlabelledBigRamseyBound_ge_exactUnmarkedDiaryCount
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    (t : Nat)
    (hBound : IsUnlabelledBigRamseyBound U A t) :
    (∑ P ∈ allIncreasingPresentations A,
      (unmarkedDiariesOfIncreasingPresentation A P).card) ≤ t := by
  classical
  obtain ⟨χ, hUnavoidable⟩ :=
    exists_unavoidableUnmarkedDiaryColour_in_universal
      U hUniversal A
  let colour : Finset Nat →
      Option (↑(allGenuineUnmarkedDiarySources A)) :=
    fun L =>
      if h : ∃ v : GenuineFiniteEmbeddings A U,
            L = (Finset.univ : Finset (Fin a)).image v.val then
        some (χ ⟨L, h⟩)
      else none
  obtain ⟨w, palette, hCardBound, hCoverage⟩ :=
    hBound (Option (↑(allGenuineUnmarkedDiarySources A))) colour
  have hEvery (d : ↑(allGenuineUnmarkedDiarySources A)) :
      (some d : Option (↑(allGenuineUnmarkedDiarySources A))) ∈
        palette := by
    obtain ⟨v, hv⟩ := hUnavoidable w d
    let L : Finset Nat :=
      (Finset.univ : Finset (Fin a)).image (fun i => w (v.val i))
    have hReal : ∃ q : GenuineFiniteEmbeddings A U,
        L = (Finset.univ : Finset (Fin a)).image q.val :=
      ⟨v.postcompose w, rfl⟩
    have hValue : colour L = some (χ ⟨L, hReal⟩) := by
      simp only [colour, dif_pos hReal]
    have hMatch : χ ⟨L, hReal⟩ = d := by
      change χ ⟨L, hReal⟩ = d at hv
      exact hv
    have hMember := hCoverage v
    change colour L ∈ palette at hMember
    rw [hValue, hMatch] at hMember
    exact hMember
  have hInj :
      Function.Injective
        (fun d : ↑(allGenuineUnmarkedDiarySources A) =>
          (some d : Option (↑(allGenuineUnmarkedDiarySources A)))) := by
    intro x y hxy
    exact Option.some.inj hxy
  have hSubset :
      ((Finset.univ : Finset (↑(allGenuineUnmarkedDiarySources A))).image
        (fun d => (some d :
          Option (↑(allGenuineUnmarkedDiarySources A))))) ⊆
        palette := by
    intro x hx
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    exact hEvery d
  have hCard :
      (allGenuineUnmarkedDiarySources A).card ≤ palette.card := by
    calc
      (allGenuineUnmarkedDiarySources A).card =
          (Finset.univ :
            Finset (↑(allGenuineUnmarkedDiarySources A))).card := by
        simp
      _ = ((Finset.univ :
          Finset (↑(allGenuineUnmarkedDiarySources A))).image
            (fun d => (some d :
              Option (↑(allGenuineUnmarkedDiarySources A))))).card := by
        exact (Finset.card_image_of_injective _ hInj).symm
      _ ≤ palette.card := Finset.card_le_card hSubset
  rw [← unmarkedDiaryCount_eq_sum_allIncreasingPresentations A]
  exact hCard.trans hCardBound

/-- EXACT numerical characterization: the least possible big
Ramsey bound for unlabelled A-copies is the sum over all
increasing presentations of A, with NO automorphism factor. -/
theorem unlabelledBigRamseyBound_iff_exactDiaryCount_le
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    (t : Nat) :
    IsUnlabelledBigRamseyBound U A t ↔
      (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) ≤ t := by
  constructor
  · exact unlabelledBigRamseyBound_ge_exactUnmarkedDiaryCount
      U hUniversal A t
  · intro ht
    have hExact := exactUnmarkedDiaryCount_is_unlabelledBigRamseyBound
      U hUniversal A
    intro κ _ _ χ
    obtain ⟨w, palette, hCard, hCover⟩ := hExact κ χ
    exact ⟨w, palette, hCard.trans ht, hCover⟩

/-- The unlabelled diary count is a unique minimal numerical
big Ramsey degree in the finite-colouring sense. -/
theorem exactUnmarkedDiaryCount_is_unique_minimal_unlabelledBigRamseyBound
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a) :
    ∃! t : Nat,
      IsUnlabelledBigRamseyBound U A t ∧
      ∀ s : Nat, IsUnlabelledBigRamseyBound U A s → t ≤ s := by
  let N : Nat :=
    ∑ P ∈ allIncreasingPresentations A,
      (unmarkedDiariesOfIncreasingPresentation A P).card
  have hN : IsUnlabelledBigRamseyBound U A N :=
    (unlabelledBigRamseyBound_iff_exactDiaryCount_le
      U hUniversal A N).mpr (Nat.le_refl N)
  refine ⟨N, ⟨hN, ?_⟩, ?_⟩
  · intro s hBound
    exact (unlabelledBigRamseyBound_iff_exactDiaryCount_le
      U hUniversal A s).mp hBound
  · intro s hs
    apply Nat.le_antisymm
    · exact hs.2 N hN
    · exact (unlabelledBigRamseyBound_iff_exactDiaryCount_le
        U hUniversal A s).mp hs.1

end ATRFiniteDecoder
end ThreeUniformDiaries
