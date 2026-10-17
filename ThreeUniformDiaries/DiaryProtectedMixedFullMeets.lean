import ThreeUniformDiaries.DiaryProtectedSplitSingletonMeets
import ThreeUniformDiaries.DiaryOnePassOldSplitWitnessTransport

/-!
# Protected numerical one-meets and mixed full two-meets

For numerical singleton meets, the source-to-target one-pass map is
already exact in either of two situations:
* at least one endpoint is an old split (#647); or
* distinct leaf endpoints meet at an existing old one-split (#594).

The remaining diagonal case is automatic. Packaging these three
cases allows exact preservation of a full two-type meet for any two
ordered pairs EACH containing a split, provided their two coordinate
comparisons satisfy the corresponding protected one-meet conditions.

Unlike arbitrary raw pre-diary leaf comparisons, these protected
comparisons cannot develop a fresh one-split at a former leaf cut.
This theorem is still an explicitly scoped PROTECTED-PAIR result:
it does not construct the global finite-diary embedding, identify
all protected copies in the flip construction, or absorb every flip.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- A diagonal singleton meet equals the vertex itself, even
without diary role or E axioms. -/
theorem Ordered3Graph.oneMeetLevel_self
    (H : Ordered3Graph Nat) (u : Nat) :
    H.oneMeetLevel u u = u := by
  classical
  apply le_antisymm
  · simpa only [min_self] using H.oneMeetLevel_le_min u u
  · apply Nat.le_findGreatest (by simp)
    intro a b hab hb
    rfl

/-- Exact singleton meet transport when either member is a split,
both are the same vertex, or both are leaves with a noncapped meet
at an ACTUAL source one-split. This captures precisely the
remaining protected-leaf hypothesis. -/
theorem onePass_protected_oneMeet_preserved
    (P : RolePrediary H) (u v : Nat)
    (hu3 : 3 ≤ u) (hv3 : 3 ≤ v)
    (hProtected :
      IsDiarySplit H u ∨ IsDiarySplit H v ∨
      u = v ∨
      (∃ m : Nat, IsOneSplit H m ∧
        IsLeaf H u ∧ IsLeaf H v ∧
        m < u ∧ m < v ∧
        H.oneMeetLevel u v = m)) :
    (onePassRawTarget H).oneMeetLevel
        (onePassOldImage H u) (onePassOldImage H v) =
      onePassOldImage H (H.oneMeetLevel u v) := by
  rcases hProtected with hSplitU | hSplitV | heq | ⟨m, hm, hu, hv, hmu, hmv, hMeet⟩
  · exact onePass_oneMeet_preserved_of_split P u v hu3 hv3 (Or.inl hSplitU)
  · exact onePass_oneMeet_preserved_of_split P u v hu3 hv3 (Or.inr hSplitV)
  · subst v
    simp only [Ordered3Graph.oneMeetLevel_self]
  · rw [hMeet]
    exact onePass_oldOneSplit_meet_exact P m u v hm hu hv hmu hmv hMeet

/-- EXACT full two-meet preservation of mixed source pairs, if the
two coordinate singleton meets are protected (split/diagonal or
a genuine old one-split leaf meet). The auxiliary numerical meet
is already unconditional for such mixed pairs by #645.
No new "cross-role" type transport assumption is introduced. -/
theorem onePass_protected_mixed_twoMeet_preserved
    (P : RolePrediary H) (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (hb3 : 3 ≤ b)
    (hc3 : 3 ≤ c) (hd3 : 3 ≤ d)
    (hAB : IsDiarySplit H a ∨ IsDiarySplit H b)
    (hCD : IsDiarySplit H c ∨ IsDiarySplit H d)
    (hAC :
      IsDiarySplit H a ∨ IsDiarySplit H c ∨ a = c ∨
      (∃ m : Nat, IsOneSplit H m ∧
        IsLeaf H a ∧ IsLeaf H c ∧
        m < a ∧ m < c ∧ H.oneMeetLevel a c = m))
    (hBD :
      IsDiarySplit H b ∨ IsDiarySplit H d ∨ b = d ∨
      (∃ m : Nat, IsOneSplit H m ∧
        IsLeaf H b ∧ IsLeaf H d ∧
        m < b ∧ m < d ∧ H.oneMeetLevel b d = m)) :
    (onePassRawTarget H).twoMeetLevel
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) =
      onePassOldImage H (H.twoMeetLevel a b c d) := by
  exact onePass_mixed_twoMeet_of_coordinate_meets P
    a b c d hab hcd hAB hCD
    (onePass_protected_oneMeet_preserved P a c ha3 hc3 hAC)
    (onePass_protected_oneMeet_preserved P b d hb3 hd3 hBD)

/-- In particular, a pair comparison where BOTH coordinate
comparisons contain a split has an unconditional exact numerical
full two-meet, provided each pair itself contains a split. -/
theorem onePass_mixed_twoMeet_preserved_of_coordinate_splits
    (P : RolePrediary H) (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (hb3 : 3 ≤ b)
    (hc3 : 3 ≤ c) (hd3 : 3 ≤ d)
    (hAB : IsDiarySplit H a ∨ IsDiarySplit H b)
    (hCD : IsDiarySplit H c ∨ IsDiarySplit H d)
    (hAC : IsDiarySplit H a ∨ IsDiarySplit H c)
    (hBD : IsDiarySplit H b ∨ IsDiarySplit H d) :
    (onePassRawTarget H).twoMeetLevel
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) =
      onePassOldImage H (H.twoMeetLevel a b c d) := by
  exact onePass_protected_mixed_twoMeet_preserved P
    a b c d hab hcd ha3 hb3 hc3 hd3 hAB hCD
    (hAC.elim (fun ha => Or.inl ha) (fun hc => Or.inr (Or.inl hc)))
    (hBD.elim (fun hb => Or.inl hb) (fun hd => Or.inr (Or.inl hd)))

end DiaryLeafPriority
end ThreeUniformDiaries
