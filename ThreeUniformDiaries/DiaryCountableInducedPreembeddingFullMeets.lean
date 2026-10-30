import ThreeUniformDiaries.DiaryFiniteInducedMeetsIntoCountable
import ThreeUniformDiaries.DiaryFiniteInducedMarkerPrefix
import ThreeUniformDiaries.DiaryFiniteMarkerAuxMeetTransportCriterion

/-!
# Exact mixed meets for induced countable diary preembeddings

The existing countable diary preembedding API fixes markers,
preserves roles and all genuine leaf meets, but does NOT assert
mixed split-containing numerical meet preservation. If its
underlying map is ALSO induced on every increasing source triple,
the E1--E5 edge-shape dichotomy upgrades it to all nonmarker
singleton and full pair meets.

The proof requires no finite truncation of the target and no
hypothetical convexity or all-cut type transport. Source and
target RoleDiary permitted-edge axioms imply each mixed
singleton/auxiliary meet is marker-small (<3) or capped.
The induced edge table fixes the marker tests, and the audited
marker-dichotomy transport lemmas preserve the exact meet.

The theorem is conditional on a genuinely induced countable
preembedding. It does NOT construct coherent finite-stage maps
or prove unrestricted countable-source unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {f : Nat → Nat}

/-- Two genuine countable source nonmarker vertices which are
not both leaves contain a real one-split or two-split. -/
theorem RoleDiary.pair_contains_split_of_not_both_leaf
    (DH : RoleDiary H) (u v : Nat)
    (hu3 : 3 ≤ u) (hv3 : 3 ≤ v)
    (hNot : ¬ (IsLeaf H u ∧ IsLeaf H v)) :
    IsDiarySplit H u ∨ IsDiarySplit H v := by
  rcases DH.role_valid u hu3 with huLeaf | huOne | huTwo
  · rcases DH.role_valid v hv3 with hvLeaf | hvOne | hvTwo
    · exact False.elim (hNot ⟨huLeaf,hvLeaf⟩)
    · exact Or.inr (Or.inl hvOne)
    · exact Or.inr (Or.inr hvTwo)
  · exact Or.inl (Or.inl huOne)
  · exact Or.inl (Or.inr huTwo)

/-- When the source pair has a split, its first singleton
disagreement is marker-small or capped, both before and after
a genuine induced countable diary preembedding. The marker
prefix tests force EXACT numerical meet transport. -/
theorem countable_induced_mixed_oneMeet_preserved
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : DiaryPreembeddingSpec H K f)
    (hInduced : ∀ a b c : Nat, a < b → b < c →
      (K.edge (f a) (f b) (f c) ↔ H.edge a b c))
    (u v : Nat) (hu3 : 3 ≤ u) (hv3 : 3 ≤ v)
    (hSplit : IsDiarySplit H u ∨ IsDiarySplit H v) :
    K.oneMeetLevel (f u) (f v) =
      f (H.oneMeetLevel u v) := by
  have hSrcU : IsLeaf H u ∨ IsDiarySplit H u := by
    rcases DH.role_valid u hu3 with huLeaf | huOne | huTwo
    · exact Or.inl huLeaf
    · exact Or.inr (Or.inl huOne)
    · exact Or.inr (Or.inr huTwo)
  have hSrcV : IsLeaf H v ∨ IsDiarySplit H v := by
    rcases DH.role_valid v hv3 with hvLeaf | hvOne | hvTwo
    · exact Or.inl hvLeaf
    · exact Or.inr (Or.inl hvOne)
    · exact Or.inr (Or.inr hvTwo)
  have hRolesU := P.role_iff DH u hu3
  have hRolesV := P.role_iff DH v hv3
  have hDstU : IsLeaf K (f u) ∨ IsDiarySplit K (f u) := by
    rcases hSrcU with hl | hs
    · exact Or.inl (hRolesU.1.mpr hl)
    · rcases hs with ho | ht
      · exact Or.inr (Or.inl (hRolesU.2.1.mpr ho))
      · exact Or.inr (Or.inr (hRolesU.2.2.mpr ht))
  have hDstV : IsLeaf K (f v) ∨ IsDiarySplit K (f v) := by
    rcases hSrcV with hl | hs
    · exact Or.inl (hRolesV.1.mpr hl)
    · rcases hs with ho | ht
      · exact Or.inr (Or.inl (hRolesV.2.1.mpr ho))
      · exact Or.inr (Or.inr (hRolesV.2.2.mpr ht))
  have hDstSplit : IsDiarySplit K (f u) ∨ IsDiarySplit K (f v) := by
    rcases hSplit with hs | hs
    · rcases hs with ho | ht
      · exact Or.inl (Or.inl (hRolesU.2.1.mpr ho))
      · exact Or.inl (Or.inr (hRolesU.2.2.mpr ht))
    · rcases hs with ho | ht
      · exact Or.inr (Or.inl (hRolesV.2.1.mpr ho))
      · exact Or.inr (Or.inr (hRolesV.2.2.mpr ht))
  have hFu3 : 3 ≤ f u := by
    have h := P.strictMono (show 2 < u by omega)
    rw [P.marker_two] at h
    omega
  have hFv3 : 3 ≤ f v := by
    have h := P.strictMono (show 2 < v by omega)
    rw [P.marker_two] at h
    omega
  have hSourceCase := E_split_oneMeet_small_or_capped
    DH.permitted_edge u v hu3 hv3 hSrcU hSrcV hSplit
  have hTargetCase := E_split_oneMeet_small_or_capped
    DK.permitted_edge (f u) (f v) hFu3 hFv3
      hDstU hDstV hDstSplit
  have hMarkers : ∀ x : Nat, x < 3 → f x = x := by
    intro x hx
    exact fixed_three_markers
      P.marker_zero P.marker_one P.marker_two x hx
  have hPrefix : ∀ l : Nat, l ≤ 3 →
      (K.SameOneTypeBelow l (f u) (f v) ↔
        H.SameOneTypeBelow l u v) := by
    intro l hl
    exact marker_oneType_iff_of_induced
      (A := H) (T := K) (n := max u v + 1) (f := f)
      P.marker_zero P.marker_one P.marker_two
      (by intro a b c hab hbc _hcn
          exact hInduced a b c hab hbc)
      l u v hl hu3 (by omega) hv3 (by omega)
  exact oneMeet_preserved_of_marker_dichotomy
    (A := H) (T := K) (f := f)
    P.strictMono hMarkers u v hu3 hv3
    hSourceCase hTargetCase hPrefix

/-- For full pairs with at least one source split endpoint,
the exact auxiliary first-disagreement level is preserved
under induced countable diary preembeddings. -/
theorem countable_induced_mixed_auxMeet_preserved
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : DiaryPreembeddingSpec H K f)
    (hInduced : ∀ a b c : Nat, a < b → b < c →
      (K.edge (f a) (f b) (f c) ↔ H.edge a b c))
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (hc3 : 3 ≤ c)
    (hSomeSplit :
      (IsDiarySplit H a ∨ IsDiarySplit H b) ∨
      (IsDiarySplit H c ∨ IsDiarySplit H d)) :
    K.auxMeetLevel (f a) (f b) (f c) (f d) =
      f (H.auxMeetLevel a b c d) := by
  have hb3 : 3 ≤ b := by omega
  have hd3 : 3 ≤ d := by omega
  have hF3 (u : Nat) (hu3 : 3 ≤ u) : 3 ≤ f u := by
    have h := P.strictMono (show 2 < u by omega)
    rw [P.marker_two] at h
    omega
  have hSplitImage : ∀ u : Nat, 3 ≤ u →
      IsDiarySplit H u → IsDiarySplit K (f u) := by
    intro u hu3 hs
    have hr := P.role_iff DH u hu3
    rcases hs with ho | ht
    · exact Or.inl (hr.2.1.mpr ho)
    · exact Or.inr (hr.2.2.mpr ht)
  have hTargetMixed :
      (IsDiarySplit K (f a) ∨ IsDiarySplit K (f b)) ∨
      (IsDiarySplit K (f c) ∨ IsDiarySplit K (f d)) := by
    rcases hSomeSplit with (ha | hb) | (hc | hd)
    · exact Or.inl (Or.inl (hSplitImage a ha3 ha))
    · exact Or.inl (Or.inr (hSplitImage b hb3 hb))
    · exact Or.inr (Or.inl (hSplitImage c hc3 hc))
    · exact Or.inr (Or.inr (hSplitImage d hd3 hd))
  have hSourceCase :=
    DH.mixed_auxMeet_small_or_capped
      a b c d ha3 hab hc3 hcd hSomeSplit
  have hTargetCase :=
    DK.mixed_auxMeet_small_or_capped
      (f a) (f b) (f c) (f d)
      (hF3 a ha3) (P.strictMono hab)
      (hF3 c hc3) (P.strictMono hcd)
      hTargetMixed
  have hMarkers : ∀ x : Nat, x < 3 → f x = x := by
    intro x hx
    exact fixed_three_markers
      P.marker_zero P.marker_one P.marker_two x hx
  have hPrefix : ∀ l : Nat, l ≤ 3 →
      (K.SameAuxTypeBelow l (f a) (f b) (f c) (f d) ↔
        H.SameAuxTypeBelow l a b c d) := by
    intro l hl
    exact marker_auxType_iff_of_induced
      (A := H) (T := K) (n := max b d + 1) (f := f)
      P.marker_zero P.marker_one P.marker_two
      (by intro u v w huv hvw _hwn
          exact hInduced u v w huv hvw)
      l a b c d hl ha3 hab (by omega) hc3 hcd (by omega)
  exact auxMeet_preserved_of_marker_dichotomy
    (A := H) (T := K) (f := f)
    P.strictMono hMarkers a b c d ha3 hc3
    hSourceCase hTargetCase hPrefix

/-- All nonmarker singleton numerical meets survive a globally
induced countable diary preembedding. -/
theorem countable_induced_all_oneMeet_preserved
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : DiaryPreembeddingSpec H K f)
    (hInduced : ∀ a b c : Nat, a < b → b < c →
      (K.edge (f a) (f b) (f c) ↔ H.edge a b c))
    (u v : Nat) (hu3 : 3 ≤ u) (hv3 : 3 ≤ v) :
    K.oneMeetLevel (f u) (f v) =
      f (H.oneMeetLevel u v) := by
  by_cases hLeaf : IsLeaf H u ∧ IsLeaf H v
  · exact P.leaf_one_meet u v hLeaf.1 hLeaf.2
  · have hSplit := DH.pair_contains_split_of_not_both_leaf
      u v hu3 hv3 hLeaf
    exact countable_induced_mixed_oneMeet_preserved
      DH DK P hInduced u v hu3 hv3 hSplit

/-- Every ordered-pair numerical meet, including arbitrary mixed
split/leaf tuples, survives a globally induced preembedding. -/
theorem countable_induced_all_twoMeet_preserved
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : DiaryPreembeddingSpec H K f)
    (hInduced : ∀ a b c : Nat, a < b → b < c →
      (K.edge (f a) (f b) (f c) ↔ H.edge a b c))
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (hc3 : 3 ≤ c) :
    K.twoMeetLevel (f a) (f b) (f c) (f d) =
      f (H.twoMeetLevel a b c d) := by
  have hb3 : 3 ≤ b := by omega
  have hd3 : 3 ≤ d := by omega
  by_cases hLeaves :
      (IsLeaf H a ∧ IsLeaf H b) ∧
      (IsLeaf H c ∧ IsLeaf H d)
  · exact P.leaf_two_meet a b c d hab hcd
      hLeaves.1.1 hLeaves.1.2
      hLeaves.2.1 hLeaves.2.2
  · have hMixed :
        (IsDiarySplit H a ∨ IsDiarySplit H b) ∨
        (IsDiarySplit H c ∨ IsDiarySplit H d) := by
      by_cases hAB : IsLeaf H a ∧ IsLeaf H b
      · have hCD : ¬ (IsLeaf H c ∧ IsLeaf H d) := by
          intro hc
          exact hLeaves ⟨hAB,hc⟩
        exact Or.inr (DH.pair_contains_split_of_not_both_leaf
          c d hc3 hd3 hCD)
      · exact Or.inl (DH.pair_contains_split_of_not_both_leaf
          a b ha3 hb3 hAB)
    have hFirst := countable_induced_all_oneMeet_preserved
      DH DK P hInduced a c ha3 hc3
    have hSecond := countable_induced_all_oneMeet_preserved
      DH DK P hInduced b d hb3 hd3
    have hAux := countable_induced_mixed_auxMeet_preserved
      DH DK P hInduced a b c d hab hcd ha3 hc3 hMixed
    have hMapMin : ∀ x y : Nat,
        min (f x) (f y) = f (min x y) := by
      intro x y
      have hMono := P.strictMono.monotone
      rcases le_total x y with hxy | hyx
      · rw [min_eq_left (hMono hxy), min_eq_left hxy]
      · rw [min_eq_right (hMono hyx), min_eq_right hyx]
    rw [K.twoMeetLevel_eq_min (f a) (f b) (f c) (f d)
        (P.strictMono hab) (P.strictMono hcd),
      H.twoMeetLevel_eq_min a b c d hab hcd]
    rw [hFirst,hSecond,hAux]
    simp only [hMapMin]

/-- The pointwise map of an induced countable diary preembedding
is a genuine ordered graph embedding, and it preserves all
nonmarker singleton and full ordered-pair meet levels. This
is conditional only on the LITERAL induced-edge hypothesis. -/
theorem DiaryPreembeddingSpec.all_numerical_meets_of_induced
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : DiaryPreembeddingSpec H K f)
    (hInduced : ∀ a b c : Nat, a < b → b < c →
      (K.edge (f a) (f b) (f c) ↔ H.edge a b c)) :
    (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
      K.oneMeetLevel (f u) (f v) = f (H.oneMeetLevel u v)) ∧
    (∀ a b c d : Nat, a < b → c < d →
      3 ≤ a → 3 ≤ c →
      K.twoMeetLevel (f a) (f b) (f c) (f d) =
        f (H.twoMeetLevel a b c d)) := by
  refine ⟨?_,?_⟩
  · intro u v hu hv
    exact countable_induced_all_oneMeet_preserved
      DH DK P hInduced u v hu hv
  · intro a b c d hab hcd ha hc
    exact countable_induced_all_twoMeet_preserved
      DH DK P hInduced a b c d hab hcd ha hc

end DiaryLeafPriority
end ThreeUniformDiaries
