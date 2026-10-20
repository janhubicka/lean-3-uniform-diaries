import ThreeUniformDiaries.DiaryFiniteInducedMixedSingletonMeets
import ThreeUniformDiaries.DiaryFiniteMarkerAuxMeetTransportCriterion
import ThreeUniformDiaries.DiaryFiniteFlipTargetTransport

/-!
# All finite meets under an induced leaf preembedding

The verified finite target-flip pullback yields a genuine source
flip whose entire ternary relation is induced from the target flip.
It also has a leaf preembedding preserving all leaf-only numerical
meets. An induced map is not automatically a type-respecting
embedding across OMITTED target vertices, so mixed meets need an
independent argument.

We now combine the precise safe ingredients:
* leaf/leaf singleton and ordered-pair meets from the genuine
  finite leaf preembedding;
* split-containing singleton meets from the E-only marker
  dichotomy and induced marker roles/prefixes;
* auxiliary meets involving a split from the E-only mixed-pair
  dichotomy and induced marker auxiliary prefixes.

Both coordinate singleton meets plus the auxiliary meet determine
every full ordered-pair meet. Therefore a genuinely induced finite
leaf preembedding between finite V/E pre-diaries preserves ALL
numerical singleton/full-pair meets on the finite source frame.

The induced hypothesis must be checked for the specific target
flip pullback; it is NEVER inferred merely from leaf inducedness.
This theorem does not imply that the original UNFLIPPED source
embeds into every target flip.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A T : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}

/-- A finite V/E pre-diary pair not consisting entirely of leaves
must contain a genuine one-split or two-split. -/
theorem FiniteRolePrediaryBlock.pair_contains_split_of_not_both_leaf
    (PA : FiniteRolePrediaryBlock A n)
    (u v : Nat)
    (hu3 : 3 ≤ u) (hun : u < n)
    (hv3 : 3 ≤ v) (hvn : v < n)
    (hNot : ¬ (IsLeaf A u ∧ IsLeaf A v)) :
    IsDiarySplit A u ∨ IsDiarySplit A v := by
  rcases PA.role_valid u hu3 hun with huLeaf | huOne | huTwo
  · rcases PA.role_valid v hv3 hvn with hvLeaf | hvOne | hvTwo
    · exact False.elim (hNot ⟨huLeaf,hvLeaf⟩)
    · exact Or.inr (Or.inl hvOne)
    · exact Or.inr (Or.inr hvTwo)
  · exact Or.inl (Or.inl huOne)
  · exact Or.inl (Or.inr huTwo)

/-- Exact auxiliary meet transport if at least one compared
ordered pair contains a split. Three marker prefix comparisons
and E/V3 small-or-capped dichotomies suffice; no all-cut type
reflection, target split witness or source S1/S2 is assumed. -/
theorem finite_induced_mixed_auxMeet_preserved
    (PA : FiniteRolePrediaryBlock A n)
    (PT : FiniteRolePrediaryBlock T k)
    (Q : FiniteLeafPreembedding A T n k f)
    (hInduced : ∀ u v w : Nat, u < v → v < w → w < n →
      (T.edge (f u) (f v) (f w) ↔ A.edge u v w))
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (han : a < n)
    (hbn : b < n)
    (hc3 : 3 ≤ c) (hcn : c < n)
    (hdn : d < n)
    (hSomeSplit :
      (IsDiarySplit A a ∨ IsDiarySplit A b) ∨
      (IsDiarySplit A c ∨ IsDiarySplit A d)) :
    T.auxMeetLevel (f a) (f b) (f c) (f d) =
      f (A.auxMeetLevel a b c d) := by
  have hb3 : 3 ≤ b := by omega
  have hd3 : 3 ≤ d := by omega
  have hF3 (u : Nat) (hu3 : 3 ≤ u) : 3 ≤ f u := by
    have hLt := Q.strictMono (show 2 < u by omega)
    rw [Q.marker_two] at hLt
    omega
  have hSplitImage : ∀ u : Nat, 3 ≤ u → u < n →
      IsDiarySplit A u → IsDiarySplit T (f u) := by
    intro u hu3 hun hs
    have hr := finite_induced_marker_roles_iff
      (A := A) (T := T) (n := n) (f := f)
      Q.strictMono Q.marker_zero Q.marker_one Q.marker_two
      hInduced u hu3 hun
    rcases hs with hOne | hTwo
    · exact Or.inl (hr.2.1.mpr hOne)
    · exact Or.inr (hr.2.2.mpr hTwo)
  have hTargetMixed :
      (IsDiarySplit T (f a) ∨ IsDiarySplit T (f b)) ∨
      (IsDiarySplit T (f c) ∨ IsDiarySplit T (f d)) := by
    rcases hSomeSplit with (ha | hb) | (hc | hd)
    · exact Or.inl (Or.inl (hSplitImage a ha3 han ha))
    · exact Or.inl (Or.inr (hSplitImage b hb3 hbn hb))
    · exact Or.inr (Or.inl (hSplitImage c hc3 hcn hc))
    · exact Or.inr (Or.inr (hSplitImage d hd3 hdn hd))
  have hSourceCase := PA.mixed_auxMeet_small_or_capped
    a b c d ha3 hab hbn hc3 hcd hdn hSomeSplit
  have hTargetCase := PT.mixed_auxMeet_small_or_capped
    (f a) (f b) (f c) (f d)
    (hF3 a ha3) (Q.strictMono hab) (Q.image_bound b hbn)
    (hF3 c hc3) (Q.strictMono hcd) (Q.image_bound d hdn)
    hTargetMixed
  have hMarker : ∀ t : Nat, t < 3 → f t = t := by
    intro t ht
    exact fixed_three_markers
      Q.marker_zero Q.marker_one Q.marker_two t ht
  have hPrefix : ∀ l : Nat, l ≤ 3 →
      (T.SameAuxTypeBelow l (f a) (f b) (f c) (f d) ↔
        A.SameAuxTypeBelow l a b c d) := by
    intro l hl
    exact marker_auxType_iff_of_induced
      (A := A) (T := T) (n := n) (f := f)
      Q.marker_zero Q.marker_one Q.marker_two
      hInduced l a b c d hl ha3 hab hbn hc3 hcd hdn
  exact auxMeet_preserved_of_marker_dichotomy
    (A := A) (T := T) (f := f)
    Q.strictMono hMarker a b c d ha3 hc3
    hSourceCase hTargetCase hPrefix

/-- The leaf preembedding already preserves singleton meets
between leaves. The induced-triple argument supplies precisely
the missing split-containing cases. Together every finite
nonmarker singleton meet is preserved numerically. -/
theorem finite_induced_all_oneMeet_preserved
    (PA : FiniteRolePrediaryBlock A n)
    (PT : FiniteRolePrediaryBlock T k)
    (Q : FiniteLeafPreembedding A T n k f)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c))
    (u v : Nat)
    (hu3 : 3 ≤ u) (hun : u < n)
    (hv3 : 3 ≤ v) (hvn : v < n) :
    T.oneMeetLevel (f u) (f v) =
      f (A.oneMeetLevel u v) := by
  by_cases hLeaves : IsLeaf A u ∧ IsLeaf A v
  · exact Q.leaf_oneMeet u v hu3 hun hv3 hvn hLeaves.1 hLeaves.2
  · have hSplit := PA.pair_contains_split_of_not_both_leaf
      u v hu3 hun hv3 hvn hLeaves
    exact finite_induced_mixed_oneMeet_preserved
      PA PT Q.strictMono
      Q.marker_zero Q.marker_one Q.marker_two
      hInduced u v hu3 hun hv3 hvn hSplit

/-- Full meet preservation for ANY TWO increasing source
nonmarker pairs, including split/leaf and capped cases.
The all-leaf case is exactly the leaf preembedding field.
Otherwise all three numeric meet components are transported
through a common strictly increasing marker-fixing map. -/
theorem finite_induced_all_twoMeet_preserved
    (PA : FiniteRolePrediaryBlock A n)
    (PT : FiniteRolePrediaryBlock T k)
    (Q : FiniteLeafPreembedding A T n k f)
    (hInduced : ∀ u v w : Nat, u < v → v < w → w < n →
      (T.edge (f u) (f v) (f w) ↔ A.edge u v w))
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (han : a < n)
    (hb3 : 3 ≤ b) (hbn : b < n)
    (hc3 : 3 ≤ c) (hcn : c < n)
    (hd3 : 3 ≤ d) (hdn : d < n) :
    T.twoMeetLevel (f a) (f b) (f c) (f d) =
      f (A.twoMeetLevel a b c d) := by
  by_cases hAllLeaves :
      (IsLeaf A a ∧ IsLeaf A b) ∧
      (IsLeaf A c ∧ IsLeaf A d)
  · exact Q.leaf_twoMeet a b c d hab hcd hbn hdn
      hAllLeaves.1.1 hAllLeaves.1.2
      hAllLeaves.2.1 hAllLeaves.2.2
  · have hSomeMixed :
        (IsDiarySplit A a ∨ IsDiarySplit A b) ∨
        (IsDiarySplit A c ∨ IsDiarySplit A d) := by
      by_cases hAB : IsLeaf A a ∧ IsLeaf A b
      · have hCD : ¬ (IsLeaf A c ∧ IsLeaf A d) := by
          intro hc
          exact hAllLeaves ⟨hAB,hc⟩
        exact Or.inr (PA.pair_contains_split_of_not_both_leaf
          c d hc3 hcn hd3 hdn hCD)
      · exact Or.inl (PA.pair_contains_split_of_not_both_leaf
          a b ha3 han hb3 hbn hAB)
    have hFirst := finite_induced_all_oneMeet_preserved
      PA PT Q hInduced a c ha3 han hc3 hcn
    have hSecond := finite_induced_all_oneMeet_preserved
      PA PT Q hInduced b d hb3 hbn hd3 hdn
    have hAux := finite_induced_mixed_auxMeet_preserved
      PA PT Q hInduced a b c d
      hab hcd ha3 han hbn hc3 hcn hdn hSomeMixed
    have hMapMin : ∀ x y : Nat,
        min (f x) (f y) = f (min x y) := by
      intro x y
      have hMon := Q.strictMono.monotone
      rcases le_total x y with hxy | hyx
      · rw [min_eq_left (hMon hxy), min_eq_left hxy]
      · rw [min_eq_right (hMon hyx), min_eq_right hyx]
    rw [T.twoMeetLevel_eq_min (f a) (f b) (f c) (f d)
        (Q.strictMono hab) (Q.strictMono hcd),
      A.twoMeetLevel_eq_min a b c d hab hcd]
    rw [hFirst,hSecond,hAux]
    simp only [hMapMin]

end DiaryLeafPriority
end ThreeUniformDiaries
