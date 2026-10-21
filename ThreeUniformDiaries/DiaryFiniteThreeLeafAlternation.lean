import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.DiaryFiniteEOneSplitLex
import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection

/-!
# Three interleaved leaves force both one-split orientations

Let a < b < c be leaves with the same singleton meet s on the
two adjacent pairs (a,b) and (b,c). In ANY finite pre-diary
the genuine one-split incidence at s is opposite for each
adjacent pair. Hence either the later leaf b is positive in
(a,b), or (if b is negative) the later leaf c is positive
in (b,c).

The literal V3 marker-one bits of these pairs are exactly
their right one-split incidences, by the verified E-only
LexEarlier formula.

This pattern survives EVERY genuine flip of a finite diary:
roles and both numerical singleton leaf meets are invariant.
It is a geometric candidate for small flip-absorbing target
gadgets; it does not by itself prove the general second
finite flip property or construct a complete target diary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- In an honest finite pre-diary, consecutive ordered leaf
pairs with the SAME one-split meet force a later-positive
pair on at least one side of the middle leaf.

Both the required one-split incidence and its literal V3
Devlin marker-one edge are recorded. -/
theorem finite_three_leaf_alternating_oneSplit
    {H : Ordered3Graph Nat} {k : Nat}
    (D : FiniteRolePrediaryBlock H k)
    (s a b c : Nat)
    (hs : IsOneSplit H s)
    (hsa : s < a) (hab : a < b) (hbc : b < c)
    (hck : c < k)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c)
    (hmAB : H.oneMeetLevel a b = s)
    (hmBC : H.oneMeetLevel b c = s) :
    (¬ H.edge 0 s a ∧ H.edge 0 s b ∧ H.edge 1 a b) ∨
    (¬ H.edge 0 s b ∧ H.edge 0 s c ∧ H.edge 1 b c) := by
  have hDiffAB : ¬ (H.edge 0 s a ↔ H.edge 0 s b) :=
    E_oneSplit_distinguishing_zero_bit
      D.permitted_edge s a b hs hab hsa hmAB
  have hDiffBC : ¬ (H.edge 0 s b ↔ H.edge 0 s c) :=
    E_oneSplit_distinguishing_zero_bit
      D.permitted_edge s b c hs hbc (by omega) hmBC
  have hLexAB : LexEarlier H a b ↔ H.edge 0 s b :=
    E_oneSplit_lexEarlier_iff_right
      D.permitted_edge s a b hs hab hsa hmAB
  have hLexBC : LexEarlier H b c ↔ H.edge 0 s c :=
    E_oneSplit_lexEarlier_iff_right
      D.permitted_edge s b c hs hbc (by omega) hmBC
  have hMarkerAB : H.edge 1 a b ↔ H.edge 0 s b :=
    (D.leaf_marker_one a b hab (by omega) ha hb).trans hLexAB
  have hMarkerBC : H.edge 1 b c ↔ H.edge 0 s c :=
    (D.leaf_marker_one b c hbc hck hb hc).trans hLexBC
  by_cases hPositiveB : H.edge 0 s b
  · have hNegativeA : ¬ H.edge 0 s a := by
      intro hPositiveA
      exact hDiffAB (by constructor <;> intro _ <;> assumption)
    exact Or.inl ⟨hNegativeA,hPositiveB,hMarkerAB.mpr hPositiveB⟩
  · have hPositiveC : H.edge 0 s c := by
      by_contra hNegativeC
      exact hDiffBC (iff_of_false hPositiveB hNegativeC)
    exact Or.inr
      ⟨hPositiveB,hPositiveC,hMarkerBC.mpr hPositiveC⟩

/-- The alternating-leaf orientation witness is INVARIANT under
all genuine finite target flips. The two adjacent leaf meets,
the role of s, and the three leaf roles transport literally.

This says nothing about full protected embeddings of larger
source diaries; it supplies a robust E2/V3 local pattern. -/
theorem FiniteDiaryFlip.three_leaf_alternating_oneSplit
    {B T : Ordered3Graph Nat} {k : Nat}
    (F : FiniteDiaryFlip B T k)
    (s a b c : Nat)
    (hs : IsOneSplit B s)
    (hsa : s < a) (hab : a < b) (hbc : b < c)
    (hck : c < k)
    (ha : IsLeaf B a) (hb : IsLeaf B b)
    (hc : IsLeaf B c)
    (hmAB : B.oneMeetLevel a b = s)
    (hmBC : B.oneMeetLevel b c = s) :
    (¬ T.edge 0 s a ∧ T.edge 0 s b ∧ T.edge 1 a b) ∨
    (¬ T.edge 0 s b ∧ T.edge 0 s c ∧ T.edge 1 b c) := by
  have hsk : s < k := by omega
  have hsa3 : 3 ≤ s := hs.1
  have hTs : IsOneSplit T s :=
    ((F.role_iff s hsa3 hsk).2.1).mp hs
  have hTa : IsLeaf T a :=
    ((F.role_iff a ha.1 (by omega)).1).mp ha
  have hTb : IsLeaf T b :=
    ((F.role_iff b hb.1 (by omega)).1).mp hb
  have hTc : IsLeaf T c :=
    ((F.role_iff c hc.1 hck).1).mp hc
  have hTmeetAB : T.oneMeetLevel a b = s := by
    exact (F.leaf_oneMeet a b (by omega) (by omega) ha hb).symm.trans hmAB
  have hTmeetBC : T.oneMeetLevel b c = s := by
    exact (F.leaf_oneMeet b c (by omega) hck hb hc).symm.trans hmBC
  exact finite_three_leaf_alternating_oneSplit F.target_diary.prediary
    s a b c hTs hsa hab hbc hck hTa hTb hTc hTmeetAB hTmeetBC

end DiaryLeafPriority
end ThreeUniformDiaries
