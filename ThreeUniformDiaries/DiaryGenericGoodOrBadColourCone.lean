import ThreeUniformDiaries.DiaryReservedOldColourTailDichotomy
import ThreeUniformDiaries.DiaryGenericOldE5TargetLeafRange
import ThreeUniformDiaries.DiaryFiniteCandidateOldColourDichotomy

/-!
# Track A: a monochromatic generic leaf subcopy is entirely bad or contains good generic cones

Fix one genuine source next leaf m and one old-stage map f.
Let B=oldStageTailCut H m f, the cut chosen BEFORE any next leaf.

Suppose the ORIGINAL prescribed target range F contains an ACTUAL
unordered induced copy J of the enumerated generic 3-hypergraph
whose every genuine target leaf has the SAME complete B-singleton
colour c. This is a genuinely monochromatic GENERIC reservoir,
not merely an unbounded sequence of vertices.

The already verified all-or-none old-colour theorem gives one of
two alternatives:
  * NO compatible reserved next-leaf image of colour c exists
    ANYWHERE (not merely in J);
  * beyond a finite target bound, EVERY genuine F-range leaf
    of colour c is a compatible reserved next-leaf image.

In the second case the verified generic old-E5-fibre subcopy theorem,
applied with EMPTY old pattern, refines J above that bound and
any new numerical target cutoff to a WHOLE induced generic target
subcopy in which EVERY vertex is a genuine compatible reserved
next-leaf image fixing the exact old source support.

The first alternative is real, not a technical artefact:
the separate checked bad E5-colour generic-subcopy theorem
constructs an induced generic reservoir with that alternative
for any old reserved stage having two fixed old leaves.

This is an EXACT generic cone dichotomy, but it does NOT produce
a good anchored colour, nor one fixed new leaf image compatible
through arbitrarily late SOURCE horizons. No countable diary
unavoidability or exact BRD conclusion is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- On one actual induced GENERIC target leaf subcopy J that is
homogeneous for a complete old-cut singleton colour c, the colour
is globally incompatible with the fixed old-stage extension,
OR its J-range contains arbitrarily late induced generic copies
whose EVERY leaf is an ACTUAL compatible reserved immediate
successor image in the ORIGINAL prescribed F range.

The original F and the induced J need not preserve numerical
enumeration order. The good generic copies may change with
the target cutoff M, and their independent reserved successor
maps are not claimed coherent in later SOURCE horizons. -/
theorem exists_good_generic_cones_or_no_compatible_anchor_in_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (G : GenericEnumerated3Graph)
    (J : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hJLeaves : ∀ n : Nat, IsLeaf K (J n))
    (hJInF : ∀ n : Nat, ∃ t : Nat, J n = F t)
    (hm : IsLeaf H m)
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool)
    (hJColour : ∀ n : Nat,
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) (J n) = c) :
    (∀ v : Nat, HasCompatibleReservedNextLeaf H K F f m v →
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v ≠ c) ∨
    (∀ M : Nat,
      ∃ U : Ordered3Graph.UnorderedEmbedding G.graph K,
        ∀ n : Nat,
          M < U n ∧ IsLeaf K (U n) ∧
          (∃ t : Nat, U n = F t) ∧
          HasCompatibleReservedNextLeaf H K F f m (U n)) := by
  classical
  rcases compatible_reserved_nextLeaf_colour_fibre_all_or_none
    (H := H) (K := K) (F := F) (f := f) (m := m)
    hm c with hNone | ⟨T, hGood⟩
  · exact Or.inl hNone
  · right
    intro M
    obtain ⟨U, hRange, _hOld, _hPattern⟩ :=
      exists_generic_leaf_subcopy_in_prescribed_oldE5_fibre
        G K J hJLeaves (∅ : Finset Nat) (fun _ _ => false) (max M T)
    refine ⟨U, ?_⟩
    intro n
    obtain ⟨hLate, hLeaf, t, hAtJ⟩ := hRange n
    have hAboveM : M < U n :=
      lt_of_le_of_lt (le_max_left _ _) hLate
    have hAboveT : T ≤ U n :=
      (le_max_right _ _).trans hLate.le
    have hOriginalRange : ∃ i : Nat, U n = F i := by
      obtain ⟨i, hi⟩ := hJInF t
      exact ⟨i, hAtJ.trans hi⟩
    have hColour :
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (U n) = c := by
      rw [hAtJ]
      exact hJColour t
    exact ⟨hAboveM, hLeaf, hOriginalRange,
      hGood (U n) hAboveT hLeaf hOriginalRange hColour⟩

/-- A finite-candidate variant useful in the actual relative
embedding construction. Given an ACTUAL old RESERVED stage P
and a full source RoleDiary H, the good generic alternative
produces not merely an abstract compatible next-leaf statement,
but the COMPLETE finite generator table and FutureOrderReserve
for every leaf of each late induced generic cone.

No target full RoleDiary assumption is needed for this full
candidate interface; the reduced E2/E3/E5 version additionally
requires one if desired. -/
theorem ReservedDiaryStage.exists_good_generic_finite_candidate_cones_or_no_anchor
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DH : RoleDiary H)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (G : GenericEnumerated3Graph)
    (J : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hJLeaves : ∀ n : Nat, IsLeaf K (J n))
    (hJInF : ∀ n : Nat, ∃ t : Nat, J n = F t)
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool)
    (hJColour : ∀ n : Nat,
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) (J n) = c) :
    (∀ v : Nat,
      (FiniteNewLeafCandidateCondition H K F m f v ∧
        FutureOrderReserve H (m + 1)
          (candidateNewLeafTableMap H K m f v)) →
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v ≠ c) ∨
    (∀ M : Nat,
      ∃ U : Ordered3Graph.UnorderedEmbedding G.graph K,
        ∀ n : Nat,
          M < U n ∧ IsLeaf K (U n) ∧
          (∃ t : Nat, U n = F t) ∧
          (FiniteNewLeafCandidateCondition H K F m f (U n) ∧
            FutureOrderReserve H (m + 1)
              (candidateNewLeafTableMap H K m f (U n)))) := by
  rcases exists_good_generic_cones_or_no_compatible_anchor_in_colour
    G J hJLeaves hJInF hm c hJColour with
      hNone | hGood
  · left
    intro v hCandidate
    exact hNone v
      ((P.finite_candidate_iff_compatible_next_leaf DH hm).mp
        hCandidate)
  · right
    intro M
    obtain ⟨U, hAll⟩ := hGood M
    refine ⟨U, ?_⟩
    intro n
    obtain ⟨hLate, hLeaf, hRange, hCompatible⟩ := hAll n
    exact ⟨hLate, hLeaf, hRange,
      (P.finite_candidate_iff_compatible_next_leaf DH hm).mpr
        hCompatible⟩

end DiaryLeafPriority
end ThreeUniformDiaries
