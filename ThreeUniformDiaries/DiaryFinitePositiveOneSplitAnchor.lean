import ThreeUniformDiaries.DiaryFiniteEOneSplitLex
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.DiaryFiniteLeafPreembeddingComposition

/-!
# One positive leaf determines all E2 bits at a genuine one-split

At a one-split s, V1 makes all positively incident leaves agree
on singleton types below s. The E1--E5 permitted edge shapes
forbid every incoming singleton test (x,s,z) with x>0, so
two positive leaves actually agree through the next cut s+1.

Hence the E2 incidence of any later leaf u is determined by a
single positive anchor a, namely

  E(0,s,u) iff s < oneMeetLevel(a,u).

This immediately provides transport for the ENTIRE E2 column
of s under any finite leaf preembedding preserving one-type meets
and just the one positive anchor edge. There is no assertion of
independent split controls or general flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Two leaves positive at the same actual one-split have
identical singleton types THROUGH the new split level. -/
theorem finite_oneSplit_positive_leaves_agree_next
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRolePrediaryBlock H n)
    (s a u : Nat)
    (hs : IsOneSplit H s)
    (ha : IsLeaf H a) (hu : IsLeaf H u)
    (hPosA : H.edge 0 s a)
    (hPosU : H.edge 0 s u) :
    H.SameOneTypeBelow (s+1) a u := by
  have hBelow : H.SameOneTypeBelow s a u :=
    D.one_split_coherent s a u hs ha hu hPosA hPosU
  intro x y hxy hy
  by_cases hys : y < s
  · exact hBelow hxy hys
  · have hyEq : y = s := by omega
    subst y
    by_cases hxZero : x = 0
    · subst x
      exact iff_of_true hPosA hPosU
    · have hxPos : 0 < x := by omega
      exact iff_of_false
        (E_oneSplit_no_positive_aux D.permitted_edge s x a hs hxPos)
        (E_oneSplit_no_positive_aux D.permitted_edge s x u hs hxPos)

/-- One positive leaf (a) defines the ENTIRE source E2 column
at s using the preserved numerical singleton leaf meets. -/
theorem finite_positive_oneSplit_edge_iff_later_oneMeet
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRolePrediaryBlock H n)
    (s a u : Nat)
    (hs : IsOneSplit H s)
    (ha : IsLeaf H a) (hu : IsLeaf H u)
    (hsa : s < a) (hsu : s < u)
    (hPositive : H.edge 0 s a) :
    H.edge 0 s u ↔ s < H.oneMeetLevel a u := by
  classical
  constructor
  · intro hPositiveU
    have hNext : H.SameOneTypeBelow (s+1) a u :=
      finite_oneSplit_positive_leaves_agree_next
        D s a u hs ha hu hPositive hPositiveU
    have hBound : s+1 ≤ min a u := by omega
    have hMeet : s+1 ≤ H.oneMeetLevel a u :=
      Nat.le_findGreatest hBound hNext
    omega
  · intro hLater
    have hSame : H.edge 0 s a ↔ H.edge 0 s u :=
      H.oneMeetLevel_agree a u (by omega) hLater
    exact hSame.mp hPositive

/-- A fully honest finite leaf preembedding which maps just
ONE positive source anchor to a positive target anchor at s
automatically preserves ALL E2 edges and nonedges over s.

No other split edge needs to be assumed induced. This is the
1-type partner of the positive two-split pair-anchor lemma. -/
theorem finite_leafPreembedding_oneSplit_E2_of_positive_anchor
    {A B : Ordered3Graph Nat} {n k : Nat}
    {f : Nat → Nat}
    (DA : FiniteRolePrediaryBlock A n)
    (DB : FiniteRolePrediaryBlock B k)
    (Q : FiniteLeafPreembedding A B n k f)
    (s a : Nat)
    (hs : IsOneSplit A s)
    (ha : IsLeaf A a)
    (hsa : s < a)
    (han : a < n)
    (hPositiveA : A.edge 0 s a)
    (hPositiveB : B.edge 0 (f s) (f a)) :
    ∀ u : Nat, u < n → IsLeaf A u → s < u →
      (A.edge 0 s u ↔ B.edge 0 (f s) (f u)) := by
  intro u hun hu hsu
  have hsn : s < n := by omega
  have hBs : IsOneSplit B (f s) :=
    ((Q.role_iff s hs.1 hsn).2.1).mpr hs
  have hBa : IsLeaf B (f a) :=
    ((Q.role_iff a ha.1 han).1).mpr ha
  have hBu : IsLeaf B (f u) :=
    ((Q.role_iff u hu.1 hun).1).mpr hu
  have hSource :=
    finite_positive_oneSplit_edge_iff_later_oneMeet
      DA s a u hs ha hu hsa hsu hPositiveA
  have hTarget :=
    finite_positive_oneSplit_edge_iff_later_oneMeet
      DB (f s) (f a) (f u)
      hBs hBa hBu (Q.strictMono hsa) (Q.strictMono hsu)
      hPositiveB
  have hMeet :
      B.oneMeetLevel (f a) (f u) =
        f (A.oneMeetLevel a u) :=
    Q.leaf_oneMeet a u ha.1 han hu.1 hun ha hu
  have hOrder :
      s < A.oneMeetLevel a u ↔
        f s < f (A.oneMeetLevel a u) := by
    constructor
    · intro h
      exact Q.strictMono h
    · intro h
      by_contra hn
      have hLe : A.oneMeetLevel a u ≤ s := Nat.le_of_not_gt hn
      have hFLe := Q.strictMono.monotone hLe
      omega
  calc
    A.edge 0 s u ↔ s < A.oneMeetLevel a u := hSource
    _ ↔ f s < f (A.oneMeetLevel a u) := hOrder
    _ ↔ f s < B.oneMeetLevel (f a) (f u) := by rw [hMeet]
    _ ↔ B.edge 0 (f s) (f u) := hTarget.symm

end DiaryLeafPriority
end ThreeUniformDiaries
