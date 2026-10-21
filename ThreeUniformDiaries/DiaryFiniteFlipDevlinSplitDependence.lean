import ThreeUniformDiaries.DiaryFiniteCanonicalVariableEShapes
import ThreeUniformDiaries.DiaryFiniteEOneSplitLex

/-!
# Devlin markers do not provide independent finite flip controls

For any genuine source diary A and any of its genuine flips P,
an ordered pair of source leaves u<v has the same numerical
singleton meet m in both diaries. The finite S1 clause makes
this m a genuine one-split below u.

The verified E-only lexicographic split formula reads the positive
edge (0,m,v). The two V3 Devlin markers of the pair (u,v) are
precisely that edge and its complement, in EVERY flip P.

Consequently any difference between two flips in either E4
Devlin marker edge at (1,u,v) or (2,u,v) forces a difference
in the E2 one-split edge (0,m,v). E4 bits therefore are NOT
independent additional correction coordinates.

This does not say that E2 split bits are free; the verified
two-one-split coupling gives counterexamples to that claim.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- In every genuine flip, both Devlin marker bits of a pair
of source leaves are given by the positive branch bit of their
ORIGINAL one-split meet. -/
theorem FiniteDiaryFlip.devlin_markers_of_original_oneSplit
    {A P : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A P n)
    (u v : Nat) (huv : u < v) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v) :
    (P.edge 1 u v ↔
       P.edge 0 (A.oneMeetLevel u v) v) ∧
    (P.edge 2 u v ↔
       ¬ P.edge 0 (A.oneMeetLevel u v) v) := by
  let m := A.oneMeetLevel u v
  have hun : u < n := by omega
  have hmA : IsOneSplit A m :=
    F.source_diary.singleton_meets u v huv hvn hu hv
  have hmle : m ≤ u := by
    have hBound := A.oneMeetLevel_le_min u v
    dsimp [m]
    omega
  have hmu : m < u := by
    by_contra hbad
    have hEq : m = u := by omega
    have hOneU : IsOneSplit A u := by
      simpa only [hEq] using hmA
    exact hu.2.1 hOneU.2.1
  have hmn : m < n := by omega
  have hmP : IsOneSplit P m :=
    ((F.role_iff m hmA.1 hmn).2.1).mp hmA
  have huP : IsLeaf P u :=
    ((F.role_iff u hu.1 hun).1).mp hu
  have hvP : IsLeaf P v :=
    ((F.role_iff v hv.1 hvn).1).mp hv
  have hMeetP : P.oneMeetLevel u v = m :=
    (F.leaf_oneMeet u v hun hvn hu hv).symm
  have hLex : LexEarlier P u v ↔ P.edge 0 m v :=
    E_oneSplit_lexEarlier_iff_right
      F.target_diary.prediary.permitted_edge
      m u v hmP huv hmu hMeetP
  have hMarkerOne := F.target_diary.prediary.leaf_marker_one
    u v huv hvn huP hvP
  have hMarkerTwo := F.target_diary.prediary.leaf_marker_two
    u v huv hvn huP hvP
  exact ⟨hMarkerOne.trans hLex,
    hMarkerTwo.trans (not_congr hLex)⟩

/-- If two genuine flips disagree on a Devlin marker of the
same ordered leaf pair, they must disagree on the corresponding
E2 positive one-split incidence at that pair's shared meet. -/
theorem FiniteDiaryFlip.devlin_difference_implies_oneSplit_difference
    {A P Q : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A P n)
    (G : FiniteDiaryFlip A Q n)
    (u v marker : Nat) (huv : u < v) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v)
    (hMarker : marker = 1 ∨ marker = 2)
    (hDiff : ¬ (P.edge marker u v ↔ Q.edge marker u v)) :
    ¬ (P.edge 0 (A.oneMeetLevel u v) v ↔
      Q.edge 0 (A.oneMeetLevel u v) v) := by
  have hP := F.devlin_markers_of_original_oneSplit
    u v huv hvn hu hv
  have hQ := G.devlin_markers_of_original_oneSplit
    u v huv hvn hu hv
  intro hSame
  rcases hMarker with hOne | hTwo
  · have hAt : P.edge 1 u v ↔ Q.edge 1 u v :=
      hP.1.trans (hSame.trans hQ.1.symm)
    exact hDiff (by simpa only [hOne] using hAt)
  · have hAt : P.edge 2 u v ↔ Q.edge 2 u v :=
      hP.2.trans ((not_congr hSame).trans hQ.2.symm)
    exact hDiff (by simpa only [hTwo] using hAt)

end DiaryLeafPriority
end ThreeUniformDiaries
