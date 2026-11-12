import ThreeUniformDiaries.DiaryFunctionalCandidateOldCutBound
import ThreeUniformDiaries.DiaryRelativeMultiColourTailObstruction

/-!
# Track A: one OLD-stage finite mixed colour controls all new-leaf terminal bits

Suppose an actual old admissible stage P has a proposed new-leaf
generator table at v that is merely FUNCTIONAL, not yet known to
be a genuine reserved successor. The checked candidate numerical
cut bound says EVERY supported image other than the new leaf m is
below B = oldStageTailCut H m f. This cut depends ONLY on old P.

If w has the same COMPLETE mixed singleton colour below B as v,
then every edge/nonedge with terminal new leaf v and two other
supported vertices x<y<m is preserved when replacing v by w,
provided the entire nonleaf generator table images at x,y agree.
This is an exact E2/E3/E5 terminal incidence transport statement,
including negative bits and with no separate target roles,
S1/S2 source-realization or future reserve assumptions.

It does NOT ensure the candidate generator profile agrees after
replacement, nor backward E2/E3 incidences involving newly
generated source splits and OLD source leaves. The result is a
conditional finite stability lemma, NOT a relative successor or
countable diary unavoidability theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Old-stage-fixed complete singleton-colour equality transports
all terminal triple bits for any two already supported source
vertices x<y<m whose proposed target images are in the SAME
functional numeric generator profile.

The first proposed table must be functional to certify the uniform
old-stage cut. The second table need NOT even be functional: its
nonleaf values at x,y are explicitly assumed equal to the first.
No source or target full RoleDiary axiom is required beyond the
existence of the old actual admissible stage P. -/
theorem AdmissibleCofinalDiaryStage.candidate_terminal_edge_stable_of_old_cut_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m v w : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hFunctional : FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f v))
    (hSameNonleaf : ∀ u : Nat,
      u ∈ countableDiaryFiniteSupport H (m + 1) →
      u ≠ m →
      candidateNewLeafTableMap H K m f v u =
        candidateNewLeafTableMap H K m f w u)
    (hColour :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v =
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w)
    (x y : Nat)
    (hx : x ∈ countableDiaryFiniteSupport H (m + 1))
    (hy : y ∈ countableDiaryFiniteSupport H (m + 1))
    (hxy : x < y) (hym : y < m)
    (hOrder :
      candidateNewLeafTableMap H K m f v x <
        candidateNewLeafTableMap H K m f v y) :
    (K.edge
      (candidateNewLeafTableMap H K m f v x)
      (candidateNewLeafTableMap H K m f v y) v ↔
     K.edge
      (candidateNewLeafTableMap H K m f w x)
      (candidateNewLeafTableMap H K m f w y) w) := by
  let g := candidateNewLeafTableMap H K m f v
  let h := candidateNewLeafTableMap H K m f w
  have hxNe : x ≠ m := ne_of_lt (lt_trans hxy hym)
  have hyNe : y ≠ m := ne_of_lt hym
  have hyBound : g y < oldStageTailCut H m f :=
    P.functional_candidate_other_below_oldStageTailCut
      hm hFunctional hy hyNe
  have hBit :
      (K.edge (g x) (g y) v ↔ K.edge (g x) (g y) w) :=
    same_singletonColour_forces_same_old_pair_edge
      K (oldStageTailCut H m f) (g x) (g y) v w
      hOrder hyBound hColour
  calc
    K.edge (g x) (g y) v ↔ K.edge (g x) (g y) w := hBit
    _ ↔ K.edge (h x) (h y) w := by
      have hxEq : g x = h x := hSameNonleaf x hx hxNe
      have hyEq : g y = h y := hSameNonleaf y hy hyNe
      rw [hxEq, hyEq]

/-- Equivalently, for a genuine full finite candidate at the
original new-leaf image v, the predicate saying that ALL terminal
triples H.edge x y m are inducedly correct is INVARIANT under any
replacement w with the same fixed old-stage singleton colour and
the same nonleaf numeric generator profile. The replacement
need NOT be a genuine successor: this isolates only the terminal
E2/E3/E5 incidence part of the finite candidate criterion. -/
theorem AdmissibleCofinalDiaryStage.candidate_terminal_source_bits_stable_of_old_cut_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m v w : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (C : FiniteNewLeafCandidateCondition H K F m f v)
    (hSameNonleaf : ∀ u : Nat,
      u ∈ countableDiaryFiniteSupport H (m + 1) →
      u ≠ m →
      candidateNewLeafTableMap H K m f v u =
        candidateNewLeafTableMap H K m f w u)
    (hColour :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v =
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w)
    (x y : Nat)
    (hx : x ∈ countableDiaryFiniteSupport H (m + 1))
    (hy : y ∈ countableDiaryFiniteSupport H (m + 1))
    (hxy : x < y) (hym : y < m) :
    ((H.edge x y m ↔
      K.edge
        (candidateNewLeafTableMap H K m f v x)
        (candidateNewLeafTableMap H K m f v y) v) ↔
     (H.edge x y m ↔
      K.edge
        (candidateNewLeafTableMap H K m f w x)
        (candidateNewLeafTableMap H K m f w y) w)) := by
  have hTarget :=
    P.candidate_terminal_edge_stable_of_old_cut_colour
      hm C.functional hSameNonleaf hColour x y
      hx hy hxy hym (C.ordered x y hx hy hxy)
  exact iff_congr Iff.rfl hTarget

end DiaryLeafPriority
end ThreeUniformDiaries
