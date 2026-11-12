import ThreeUniformDiaries.DiarySecondLeafMonochromaticConeCriterion
import ThreeUniformDiaries.DiaryGenericOldE5TargetLeafRange
import ThreeUniformDiaries.DiaryReservedOldColourTailDichotomy

/-!
# Track A: explicit favourable split iff a homogeneous generic cone has all-good subcopies

The fixed-colour SECOND-source-leaf theorem gives an exact three-test
criterion for unbounded valid reserved immediate successors inside
any injective genuine-leaf family J whose COMPLETE old-cut singleton
colour is constant: one E2 orientation and two numerical S1 gaps.

Suppose J is an ACTUAL unordered induced generic 3-hypergraph
subcopy inside the ORIGINAL prescribed target true-leaf range F,
all J vertices numerically later than the one fixed old root f(a),
and all J vertices have ONE complete singleton colour at the
oldStageTailCut chosen before adding the second source leaf m.

The SAME three finite tests are now equivalent to the existence,
beyond EVERY target numerical bound, of an ENTIRE induced generic
subcopy of J whose EVERY vertex is an actual target image of a
genuine reserved second-source-leaf successor fixing old f(a).

Proof:
  Forward: the exact second-leaf cone criterion gives an ACTUAL
  reserved anchor inside J. The verified complete-colour
  all-or-none theorem makes all sufficiently high J vertices
  genuine compatible successors. Refine J via the genuine
  generic E5-fibre copy theorem with EMPTY protected pair set
  to obtain induced generic subcopies arbitrarily high.
  Reverse: a single member of one all-good generic subcopy
  witnesses a genuine second-leaf successor in J. The fixed
  colour criterion forces exactly the three E2/S1 gap tests.

No nonempty good colour is postulated or proved from genericity
alone. This is the FIRST nontrivial positive local construction
conditional on an explicitly testable favourable root split.
No persistent next-leaf image through all later source horizons,
general third-leaf extension, countable diary unavoidability or
exact big Ramsey degree is inferred.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- With exactly one genuine old source leaf a and one fixed
homogeneous unordered generic target true-leaf subcopy J,
THE SAME explicit E2/root-S1 gap test is equivalent to the
existence of arbitrarily late whole induced generic subcopies
whose EVERY target leaf is an ACTUAL reserved successor at the
second source leaf m, fixing the original old source leaf.

The stronger conclusion retains literal inclusion of each
selected vertex in the ORIGINAL J range, not merely in F[Nat].
The witnesses need not agree through later source horizons. -/
theorem RoleDiary.second_leaf_generic_monochromatic_cone_good_iff_favourable_split
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F f : Nat → Nat)
    (J : Ordered3Graph.UnorderedEmbedding G.graph K)
    (a m : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (P : ReservedDiaryStage H K F m f)
    (hJLeaf : ∀ t : Nat, IsLeaf K (J t))
    (hJRange : ∀ t : Nat, ∃ i : Nat, J t = F i)
    (hAbove : ∀ t : Nat, f a < J t)
    (hMono : ∀ t : Nat,
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) (J t) =
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) (J 0)) :
    ((H.edge 0 (H.oneMeetLevel a m) m ↔
        ¬ K.edge 0 (K.oneMeetLevel (f a) (J 0)) (f a)) ∧
      H.oneMeetLevel a m ≤ K.oneMeetLevel (f a) (J 0) ∧
      K.oneMeetLevel (f a) (J 0) +
        (a - H.oneMeetLevel a m) ≤ f a) ↔
    (∀ M : Nat,
      ∃ U : Ordered3Graph.UnorderedEmbedding G.graph K,
        ∀ n : Nat,
          M < U n ∧
          (∃ t : Nat, U n = J t) ∧
          ∃ g : Nat → Nat,
            ReservedDiaryStage H K F (m + 1) g ∧
            (∀ x : Nat, x ∈ countableDiaryLeafPrefix H m →
              g x = f x) ∧
            g m = U n) := by
  classical
  let B := oldStageTailCut H m f
  have haPrefix : a ∈ countableDiaryLeafPrefix H m := by
    rw [hOld]
    simp
  have hCut : f a < B := by
    change f a <
      max ((countableDiaryFiniteSupport H m).sup f)
        ((countableDiaryLeafPrefix H m).sup f) + 1
    have hBound : f a ≤ (countableDiaryLeafPrefix H m).sup f :=
      Finset.le_sup (f := f) haPrefix
    omega
  have hIff :=
    DH.second_leaf_fixed_colour_cone_good_iff_favourable_split
      DK F f J a m B ha hm ham hOld P J.injective
      hJLeaf hJRange hCut hAbove hMono
  constructor
  · intro hFavourable
    have hUnbounded := hIff.mp hFavourable
    obtain ⟨t0, _hLate0, g0, Q0, hOld0, hNew0⟩ :=
      hUnbounded 0
    have hCompat0 : CofinalDiaryStageCompatible H m f g0 :=
      P.1.successor_compatible_of_selected_leaf_agreement Q0.1 hOld0
    have hGood0 :
        HasCompatibleReservedNextLeaf H K F f m (J t0) :=
      ⟨g0, Q0, hCompat0, hNew0⟩
    let c := DiaryLowerBoundColors.singletonColour K B (J 0)
    have hDich := compatible_reserved_nextLeaf_colour_fibre_all_or_none
      (H := H) (K := K) (F := F) (f := f) (m := m) hm c
    obtain ⟨T, hTail⟩ : ∃ T : Nat,
        ∀ w : Nat, T ≤ w →
          IsLeaf K w → (∃ i : Nat, w = F i) →
          DiaryLowerBoundColors.singletonColour K B w = c →
          HasCompatibleReservedNextLeaf H K F f m w := by
      rcases hDich with hNo | hYes
      · have hSame : DiaryLowerBoundColors.singletonColour K B (J t0) = c :=
          hMono t0
        exact False.elim ((hNo (J t0) hGood0) hSame)
      · exact hYes
    intro M
    obtain ⟨U, hURange, _hProtected, _hE5⟩ :=
      exists_generic_leaf_subcopy_in_prescribed_oldE5_fibre
        G K J hJLeaf (∅ : Finset Nat) (fun _ _ => false)
        (max M T)
    refine ⟨U, ?_⟩
    intro n
    obtain ⟨hLate, hULeaf, t, hUisJ⟩ := hURange n
    have hLarge : M < U n :=
      lt_of_le_of_lt (le_max_left _ _) hLate
    have hGeT : T ≤ U n :=
      (le_max_right _ _).trans hLate.le
    have hFRange : ∃ i : Nat, U n = F i := by
      obtain ⟨i, hi⟩ := hJRange t
      exact ⟨i, hUisJ.trans hi⟩
    have hColour : DiaryLowerBoundColors.singletonColour K B (U n) = c := by
      rw [hUisJ]
      exact hMono t
    obtain ⟨g, Q, hCompat, hAtU⟩ :=
      hTail (U n) hGeT hULeaf hFRange hColour
    have hKeep : ∀ x : Nat,
        x ∈ countableDiaryLeafPrefix H m → g x = f x := by
      intro x hx
      exact hCompat x
        (mem_finiteLeafMeetSupport_leaf H
          (countableDiaryLeafPrefix H m) x hx)
    exact ⟨hLarge, t, hUisJ, g, Q, hKeep, hAtU⟩
  · intro hGoodCones
    apply hIff.mpr
    intro M
    obtain ⟨U, hAll⟩ := hGoodCones M
    obtain ⟨hLarge, ⟨t, hUisJ⟩, g, Q, hKeep, hAtU⟩ :=
      hAll 0
    refine ⟨t, ?_, g, Q, hKeep, ?_⟩
    · rw [← hUisJ]
      exact hLarge
    · exact hAtU.trans hUisJ

end DiaryLeafPriority
end ThreeUniformDiaries
