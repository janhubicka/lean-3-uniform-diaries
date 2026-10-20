import ThreeUniformDiaries.DiaryFiniteInducedMarkerPrefix
import ThreeUniformDiaries.DiaryFiniteEOnlySplitMeetDichotomy
import ThreeUniformDiaries.DiaryFiniteMarkerMeetTransportCriterion
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface

/-!
# Mixed singleton meets of genuinely induced finite pullbacks

An induced finite source-copy map fixes the three markers and
reflects ALL edge/nonedge triples on the finite source frame.
This directly reflects the literal marker-defined leaf,
one-split and two-split roles. It also reflects the singleton
prefix comparisons at cuts 0,1,2,3 (verified marker transport).

Under E1--E5, every singleton meet involving a genuine split
is either marker-small (<3) or capped at the earlier vertex.
Applying the generic marker-dichotomy meet criterion now shows
that such meets are transported NUMERICALLY, even when the target
embedding omits intermediate vertices.

This removes a real obstruction to proving the canonical
source-flip pullback is a full finite meet embedding. The
all-leaf singleton case requires a distinct preserved-leaf
hypothesis and is not claimed in this module.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A T : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}

/-- A fully induced finite triple-map fixing 0,1,2 transports
and reflects ALL three marker-defined vertex roles. -/
theorem finite_induced_marker_roles_iff
    (hf : StrictMono f)
    (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : f 2 = 2)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c))
    (u : Nat) (hu3 : 3 ≤ u) (hun : u < n) :
    (IsLeaf T (f u) ↔ IsLeaf A u) ∧
    (IsOneSplit T (f u) ↔ IsOneSplit A u) ∧
    (IsTwoSplit T (f u) ↔ IsTwoSplit A u) := by
  have hfu3 : 3 ≤ f u := by
    have hh := hf (show 2 < u by omega)
    rw [h2] at hh
    omega
  have h01 : T.edge 0 1 (f u) ↔ A.edge 0 1 u := by
    simpa only [h0,h1] using
      (hInduced 0 1 u (by omega) (by omega) hun)
  have h02 : T.edge 0 2 (f u) ↔ A.edge 0 2 u := by
    simpa only [h0,h2] using
      (hInduced 0 2 u (by omega) (by omega) hun)
  constructor
  · constructor
    · intro ht
      exact ⟨hu3,
        fun he => ht.2.1 (h01.mpr he),
        fun he => ht.2.2 (h02.mpr he)⟩
    · intro ha
      exact ⟨hfu3,
        fun he => ha.2.1 (h01.mp he),
        fun he => ha.2.2 (h02.mp he)⟩
  constructor
  · constructor
    · intro ht
      exact ⟨hu3,h01.mp ht.2.1,
        fun he => ht.2.2 (h02.mpr he)⟩
    · intro ha
      exact ⟨hfu3,h01.mpr ha.2.1,
        fun he => ha.2.2 (h02.mp he)⟩
  · constructor
    · intro ht
      exact ⟨hu3,
        fun he => ht.2.1 (h01.mpr he),
        h02.mp ht.2.2⟩
    · intro ha
      exact ⟨hfu3,
        fun he => ha.2.1 (h01.mp he),
        h02.mpr ha.2.2⟩

/-- Exact transport of singleton meets involving a split through
a genuine induced finite source pullback. This does NOT require
agreement of types at omitted target vertices: markers suffice
because the source AND target have the E-only small/capped
dichotomy. -/
theorem finite_induced_mixed_oneMeet_preserved
    (PA : FiniteRolePrediaryBlock A n)
    (PT : FiniteRolePrediaryBlock T k)
    (hf : StrictMono f)
    (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : f 2 = 2)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c))
    (u v : Nat) (hu3 : 3 ≤ u) (hun : u < n)
    (hv3 : 3 ≤ v) (hvn : v < n)
    (hSplit : IsDiarySplit A u ∨ IsDiarySplit A v) :
    T.oneMeetLevel (f u) (f v) =
      f (A.oneMeetLevel u v) := by
  have hRolesU := finite_induced_marker_roles_iff
    (A := A) (T := T) (n := n) (f := f)
    hf h0 h1 h2 hInduced u hu3 hun
  have hRolesV := finite_induced_marker_roles_iff
    (A := A) (T := T) (n := n) (f := f)
    hf h0 h1 h2 hInduced v hv3 hvn
  have hSrcU : IsLeaf A u ∨ IsDiarySplit A u := by
    rcases PA.role_valid u hu3 hun with huLeaf | huOne | huTwo
    · exact Or.inl huLeaf
    · exact Or.inr (Or.inl huOne)
    · exact Or.inr (Or.inr huTwo)
  have hSrcV : IsLeaf A v ∨ IsDiarySplit A v := by
    rcases PA.role_valid v hv3 hvn with hvLeaf | hvOne | hvTwo
    · exact Or.inl hvLeaf
    · exact Or.inr (Or.inl hvOne)
    · exact Or.inr (Or.inr hvTwo)
  have hDstU : IsLeaf T (f u) ∨ IsDiarySplit T (f u) := by
    rcases hSrcU with hLeaf | hSplit
    · exact Or.inl (hRolesU.1.mpr hLeaf)
    · rcases hSplit with hOne | hTwo
      · exact Or.inr (Or.inl (hRolesU.2.1.mpr hOne))
      · exact Or.inr (Or.inr (hRolesU.2.2.mpr hTwo))
  have hDstV : IsLeaf T (f v) ∨ IsDiarySplit T (f v) := by
    rcases hSrcV with hLeaf | hSplit
    · exact Or.inl (hRolesV.1.mpr hLeaf)
    · rcases hSplit with hOne | hTwo
      · exact Or.inr (Or.inl (hRolesV.2.1.mpr hOne))
      · exact Or.inr (Or.inr (hRolesV.2.2.mpr hTwo))
  have hDstSplit : IsDiarySplit T (f u) ∨ IsDiarySplit T (f v) := by
    rcases hSplit with hSu | hSv
    · rcases hSu with hOne | hTwo
      · exact Or.inl (Or.inl (hRolesU.2.1.mpr hOne))
      · exact Or.inl (Or.inr (hRolesU.2.2.mpr hTwo))
    · rcases hSv with hOne | hTwo
      · exact Or.inr (Or.inl (hRolesV.2.1.mpr hOne))
      · exact Or.inr (Or.inr (hRolesV.2.2.mpr hTwo))
  have hFu3 : 3 ≤ f u := by
    have hh := hf (show 2 < u by omega)
    rw [h2] at hh
    omega
  have hFv3 : 3 ≤ f v := by
    have hh := hf (show 2 < v by omega)
    rw [h2] at hh
    omega
  have hSrcCase := E_split_oneMeet_small_or_capped
    PA.permitted_edge u v hu3 hv3 hSrcU hSrcV hSplit
  have hDstCase := E_split_oneMeet_small_or_capped
    PT.permitted_edge (f u) (f v) hFu3 hFv3
      hDstU hDstV hDstSplit
  have hMarker : ∀ x : Nat, x < 3 → f x = x := by
    intro x hx
    exact fixed_three_markers h0 h1 h2 x hx
  have hPrefix : ∀ l : Nat, l ≤ 3 →
      (T.SameOneTypeBelow l (f u) (f v) ↔
        A.SameOneTypeBelow l u v) := by
    intro l hl
    exact marker_oneType_iff_of_induced
      (A := A) (T := T) (n := n) (f := f)
      h0 h1 h2 hInduced l u v hl hu3 hun hv3 hvn
  exact oneMeet_preserved_of_marker_dichotomy
    (A := A) (T := T) (f := f)
    hf hMarker u v hu3 hv3 hSrcCase hDstCase hPrefix

end DiaryLeafPriority
end ThreeUniformDiaries
