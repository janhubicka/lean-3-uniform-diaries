import ThreeUniformDiaries.DiaryProtectedLeafTwoMeets
import ThreeUniformDiaries.DiaryProtectedCrossRolePairMeets
import ThreeUniformDiaries.DiaryProtectedMixedFullMeets
import ThreeUniformDiaries.DiaryOnePassCompleteS2

/-!
# Finite protected meet pictures and the one-pass diary completion

This file packages the FINITE portion of a protected diary copy
inside a countable V/E pre-diary. It does not identify an abstract
finite initial segment with a countable RoleDiary: doing so would
silently assume split witnesses outside the finite segment.

Instead, a finite set of original vertices is protected if:
* all its vertices are beyond the three distinguished markers;
* any two DISTINCT leaves in it have their ambient singleton meet
  at a genuine original one-split (restricted S1);
* every comparison of two ordered pairs of its leaves has ambient
  full twoMeet equal to marker 1, a genuine original two-split,
  or their COMMON first leaf (restricted S2 plus the S1 cap repair).

These are the exact ambient assumptions supplied by a finite
completed diary copy whose relevant numerical meets are protected.
The one-pass old map preserves the role/edge relations, all
singleton meets, and ALL full ordered pair meets between elements
of the finite set. The proof combines three checked cases:
  leaf/leaf pairs (#649), mixed/mixed pairs (#648), and
  split-containing versus all-leaf pairs (#651).

This is a relative protected picture theorem, not a construction
of the ambient pre-diary amalgam or every-flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat} {F : Finset Nat}

/-- Exactly the numerical splitting conditions needed to protect a
finite picture of original (nonmarker) diary vertices inside an
ambient pre-diary. No split-witness existence outside F is inferred. -/
structure FiniteProtectedMeetPicture
    (H : Ordered3Graph Nat) (F : Finset Nat) : Prop where
  above_markers : ∀ u, u ∈ F → 3 ≤ u
  singleton_split :
    ∀ u v, u ∈ F → v ∈ F →
      IsLeaf H u → IsLeaf H v → u ≠ v →
      IsOneSplit H (H.oneMeetLevel u v)
  leaf_pair_meets :
    ∀ a b c d, a ∈ F → b ∈ F → c ∈ F → d ∈ F →
      a < b → c < d →
      IsLeaf H a → IsLeaf H b → IsLeaf H c → IsLeaf H d →
      H.twoMeetLevel a b c d = 1 ∨
        IsTwoSplit H (H.twoMeetLevel a b c d) ∨
        (a = c ∧ H.twoMeetLevel a b c d = a)

namespace FiniteProtectedMeetPicture

/-- Every protected nonmarker vertex is either a leaf or one of
the two actual split roles of the ambient pre-diary. -/
theorem role
    (Q : FiniteProtectedMeetPicture H F)
    (P : RolePrediary H) {u : Nat} (hu : u ∈ F) :
    IsLeaf H u ∨ IsDiarySplit H u := by
  rcases P.role_valid u (Q.above_markers u hu) with hLeaf | hOne | hTwo
  · exact Or.inl hLeaf
  · exact Or.inr (Or.inl hOne)
  · exact Or.inr (Or.inr hTwo)

/-- On a protected finite carrier, each coordinate comparison
has exactly the alternatives required by the already verified
one-pass protected singleton meet theorem (#648). -/
theorem oneMeet_case
    (Q : FiniteProtectedMeetPicture H F)
    (P : RolePrediary H) {u v : Nat}
    (hu : u ∈ F) (hv : v ∈ F) :
    IsDiarySplit H u ∨ IsDiarySplit H v ∨ u = v ∨
      (∃ m : Nat, IsOneSplit H m ∧
        IsLeaf H u ∧ IsLeaf H v ∧
        m < u ∧ m < v ∧ H.oneMeetLevel u v = m) := by
  rcases Q.role P hu with hLeafU | hSplitU
  · rcases Q.role P hv with hLeafV | hSplitV
    · by_cases hEq : u = v
      · exact Or.inr (Or.inr (Or.inl hEq))
      · let m := H.oneMeetLevel u v
        have hM : IsOneSplit H m :=
          Q.singleton_split u v hu hv hLeafU hLeafV hEq
        have hBound : m ≤ min u v := H.oneMeetLevel_le_min u v
        have hMu : m < u := by
          have hle : m ≤ u := hBound.trans (min_le_left _ _)
          have hne : m ≠ u := by
            intro h
            have hRole : IsOneSplit H u := by
              simpa only [h] using hM
            exact hLeafU.2.1 hRole.2.1
          omega
        have hMv : m < v := by
          have hle : m ≤ v := hBound.trans (min_le_right _ _)
          have hne : m ≠ v := by
            intro h
            have hRole : IsOneSplit H v := by
              simpa only [h] using hM
            exact hLeafV.2.1 hRole.2.1
          omega
        exact Or.inr (Or.inr (Or.inr
          ⟨m, hM, hLeafU, hLeafV, hMu, hMv, rfl⟩))
    · exact Or.inr (Or.inl hSplitV)
  · exact Or.inl hSplitU

/-- If two protected vertices are not both leaves, at least one
is a genuine split. This removes all artificial role flags from
the ensuing pair-type case analysis. -/
theorem pair_contains_split
    (Q : FiniteProtectedMeetPicture H F)
    (P : RolePrediary H) {u v : Nat}
    (hu : u ∈ F) (hv : v ∈ F)
    (hNotBoth : ¬ (IsLeaf H u ∧ IsLeaf H v)) :
    IsDiarySplit H u ∨ IsDiarySplit H v := by
  rcases Q.role P hu with hLeafU | hSplitU
  · rcases Q.role P hv with hLeafV | hSplitV
    · exact False.elim (hNotBoth ⟨hLeafU, hLeafV⟩)
    · exact Or.inr hSplitV
  · exact Or.inl hSplitU

end FiniteProtectedMeetPicture

/-- Literal source-to-target numerical singleton meet preservation
on EVERY two vertices of a finite protected picture. -/
theorem onePass_finiteProtected_oneMeet_preserved
    (P : RolePrediary H) (Q : FiniteProtectedMeetPicture H F) :
    ∀ u v : Nat, u ∈ F → v ∈ F →
      (onePassRawTarget H).oneMeetLevel
          (onePassOldImage H u) (onePassOldImage H v) =
        onePassOldImage H (H.oneMeetLevel u v) := by
  intro u v hu hv
  exact onePass_protected_oneMeet_preserved P u v
    (Q.above_markers u hu) (Q.above_markers v hv)
    (Q.oneMeet_case P hu hv)

/-- Literal source-to-target full two-type meet preservation on
EVERY TWO ORDERED PAIRS of vertices of a finite protected picture.
The proof treats all-leaf, both-mixed and cross-role pairs,
with no assumptions about a source diary outside this finite set. -/
theorem onePass_finiteProtected_twoMeet_preserved
    (P : RolePrediary H) (Q : FiniteProtectedMeetPicture H F) :
    ∀ a b c d : Nat,
      a ∈ F → b ∈ F → c ∈ F → d ∈ F →
      a < b → c < d →
      (onePassRawTarget H).twoMeetLevel
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) =
        onePassOldImage H (H.twoMeetLevel a b c d) := by
  classical
  intro a b c d ha hb hc hd hab hcd
  have ha3 := Q.above_markers a ha
  have hb3 := Q.above_markers b hb
  have hc3 := Q.above_markers c hc
  have hd3 := Q.above_markers d hd
  by_cases hABLeaf : IsLeaf H a ∧ IsLeaf H b
  · by_cases hCDLeaf : IsLeaf H c ∧ IsLeaf H d
    · have hSourceCase := Q.leaf_pair_meets a b c d
        ha hb hc hd hab hcd
        hABLeaf.1 hABLeaf.2 hCDLeaf.1 hCDLeaf.2
      have hSecond : b = d ∨ IsOneSplit H (H.oneMeetLevel b d) := by
        by_cases hEq : b = d
        · exact Or.inl hEq
        · exact Or.inr
            (Q.singleton_split b d hb hd hABLeaf.2 hCDLeaf.2 hEq)
      exact onePass_protected_leaf_twoMeet_preserved P
        a b c d hab hcd
        hABLeaf.1 hABLeaf.2 hCDLeaf.1 hCDLeaf.2
        hSourceCase hSecond
    · have hCDMixed : IsDiarySplit H c ∨ IsDiarySplit H d :=
        Q.pair_contains_split P hc hd hCDLeaf
      exact onePass_crossRole_twoMeet_preserved P
        a b c d hab hcd ha3 hc3
        (Or.inr ⟨hABLeaf.1, hABLeaf.2, hCDMixed⟩)
  · have hABMixed : IsDiarySplit H a ∨ IsDiarySplit H b :=
      Q.pair_contains_split P ha hb hABLeaf
    by_cases hCDLeaf : IsLeaf H c ∧ IsLeaf H d
    · exact onePass_crossRole_twoMeet_preserved P
        a b c d hab hcd ha3 hc3
        (Or.inl ⟨hABMixed, hCDLeaf.1, hCDLeaf.2⟩)
    · have hCDMixed : IsDiarySplit H c ∨ IsDiarySplit H d :=
        Q.pair_contains_split P hc hd hCDLeaf
      exact onePass_protected_mixed_twoMeet_preserved P
        a b c d hab hcd ha3 hb3 hc3 hd3 hABMixed hCDMixed
        (Q.oneMeet_case P ha hc)
        (Q.oneMeet_case P hb hd)

/-- Relative finite protected-completion statement at the exact
numerical-meet level: the actual one-pass target is a full diary,
while the protected finite original set retains *all* singleton
and full two-type meets. It does not construct a finite target
diary, nor amalgamate any prescribed flips. -/
theorem onePass_completes_finiteProtected_meet_picture
    (P : RolePrediary H) (Q : FiniteProtectedMeetPicture H F) :
    RoleDiary (onePassRawTarget H) ∧
    (∀ u v : Nat, u ∈ F → v ∈ F →
      (onePassRawTarget H).oneMeetLevel
          (onePassOldImage H u) (onePassOldImage H v) =
        onePassOldImage H (H.oneMeetLevel u v)) ∧
    (∀ a b c d : Nat,
      a ∈ F → b ∈ F → c ∈ F → d ∈ F →
      a < b → c < d →
      (onePassRawTarget H).twoMeetLevel
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) =
        onePassOldImage H (H.twoMeetLevel a b c d)) := by
  exact ⟨onePassRawTarget_isDiary P,
    onePass_finiteProtected_oneMeet_preserved P Q,
    onePass_finiteProtected_twoMeet_preserved P Q⟩

end DiaryLeafPriority
end ThreeUniformDiaries
