import ThreeUniformDiaries.DiaryFiniteLeafMeetTwoSplitDisagreement
import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection

/-!
# Three leaf pairs force a positive two-split incidence

A full type meet of two genuine leaf pairs exactly at a two-split
s forces their E3-incidence bits at s to differ. This follows
from the verified E1--E5 two-split first-disagreement lemma;
the difference cannot occur in the singleton coordinates.

If three ordered leaf pairs p,q,r have full meets p^q=q^r=s,
their E3 bits alternate. In particular q or r is positive,
and its predecessor pair is negative. This persists under ALL
genuine diary flips since roles and numerical leaf-pair meets
are invariant.

This is the two-type analogue of the alternating three-leaf
one-split gadget. It is a necessary local building block for a
non-rigid 2-split flip absorber, not a complete general geometry.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- At a genuine two-split with three ordered pairs whose
successive full pair-type meets are exactly that split,
one of the second or third pairs is positively incident,
while its predecessor is negative. No independence of E3
flip bits is asserted. -/
theorem finite_three_pair_alternating_twoSplit
    {H : Ordered3Graph Nat} {k : Nat}
    (D : FiniteRolePrediaryBlock H k)
    (s a b c d e f : Nat)
    (hs : IsTwoSplit H s)
    (hsa : s < a) (hsc : s < c) (hse : s < e)
    (hab : a < b) (hcd : c < d) (hef : e < f)
    (hbk : b < k) (hdk : d < k) (hfk : f < k)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (he : IsLeaf H e) (hf : IsLeaf H f)
    (hMeet01 : H.twoMeetLevel a b c d = s)
    (hMeet12 : H.twoMeetLevel c d e f = s) :
    (¬ H.edge s a b ∧ H.edge s c d) ∨
    (¬ H.edge s c d ∧ H.edge s e f) := by
  have hDiff01 : ¬ (H.edge s a b ↔ H.edge s c d) :=
    E_twoSplit_pair_aux_distinguishes
      D.permitted_edge s a b c d hs hsa hsc hMeet01
  have hDiff12 : ¬ (H.edge s c d ↔ H.edge s e f) :=
    E_twoSplit_pair_aux_distinguishes
      D.permitted_edge s c d e f hs hsc hse hMeet12
  by_cases hMiddle : H.edge s c d
  · have hFirstNegative : ¬ H.edge s a b := by
      intro hFirst
      exact hDiff01 ⟨fun _ => hMiddle, fun _ => hFirst⟩
    exact Or.inl ⟨hFirstNegative,hMiddle⟩
  · have hLastPositive : H.edge s e f := by
      by_contra hLast
      exact hDiff12 (iff_of_false hMiddle hLast)
    exact Or.inr ⟨hMiddle,hLastPositive⟩

/-- Three-pair alternating E3 incidence in EVERY genuine finite
flip, from the same unchanged split role and leaf-pair meets.
The pairs can share leaves; no false disjointness assumption. -/
theorem FiniteDiaryFlip.three_pair_alternating_twoSplit
    {B T : Ordered3Graph Nat} {k : Nat}
    (F : FiniteDiaryFlip B T k)
    (s a b c d e f : Nat)
    (hs : IsTwoSplit B s)
    (hsa : s < a) (hsc : s < c) (hse : s < e)
    (hab : a < b) (hcd : c < d) (hef : e < f)
    (hbk : b < k) (hdk : d < k) (hfk : f < k)
    (ha : IsLeaf B a) (hb : IsLeaf B b)
    (hc : IsLeaf B c) (hd : IsLeaf B d)
    (he : IsLeaf B e) (hf : IsLeaf B f)
    (hMeet01 : B.twoMeetLevel a b c d = s)
    (hMeet12 : B.twoMeetLevel c d e f = s) :
    (¬ T.edge s a b ∧ T.edge s c d) ∨
    (¬ T.edge s c d ∧ T.edge s e f) := by
  have hsk : s < k := by omega
  have hTs : IsTwoSplit T s :=
    ((F.role_iff s hs.1 hsk).2.2).mp hs
  have hTa : IsLeaf T a :=
    ((F.role_iff a ha.1 (by omega)).1).mp ha
  have hTb : IsLeaf T b :=
    ((F.role_iff b hb.1 hbk).1).mp hb
  have hTc : IsLeaf T c :=
    ((F.role_iff c hc.1 (by omega)).1).mp hc
  have hTd : IsLeaf T d :=
    ((F.role_iff d hd.1 hdk).1).mp hd
  have hTe : IsLeaf T e :=
    ((F.role_iff e he.1 (by omega)).1).mp he
  have hTf : IsLeaf T f :=
    ((F.role_iff f hf.1 hfk).1).mp hf
  have hTMeet01 : T.twoMeetLevel a b c d = s :=
    (F.leaf_twoMeet a b c d hab hcd hbk hdk
      ha hb hc hd).symm.trans hMeet01
  have hTMeet12 : T.twoMeetLevel c d e f = s :=
    (F.leaf_twoMeet c d e f hcd hef hdk hfk
      hc hd he hf).symm.trans hMeet12
  exact finite_three_pair_alternating_twoSplit
    F.target_diary.prediary s a b c d e f
    hTs hsa hsc hse hab hcd hef
    hbk hdk hfk hTa hTb hTc hTd hTe hTf
    hTMeet01 hTMeet12

end DiaryLeafPriority
end ThreeUniformDiaries
