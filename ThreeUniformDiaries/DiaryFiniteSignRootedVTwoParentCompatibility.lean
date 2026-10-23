import ThreeUniformDiaries.DiaryFiniteSignRootedPrefixCodes
import ThreeUniformDiaries.DiaryFiniteTwoSplitParentProfile

/-!
# Cross-flip V2 parent compatibility at a sign-rooted shared two-split

Let P,Q be genuine flips of one finite source diary A. Fix a
source two-split s, and assume P,Q have the same GLOBAL marker-one
sign and the same S2 witness bits for all earlier source 2-splits
t<s. At s itself, their E3 witness bits may DISAGREE.

The verified sign-rooted prefix theorem gives exact equality of
the complete source two-type predecessor codes below cut s on
a fixed S2 witness pair. Independently, the verified S2 positive
parent-profile lemma shows that in EITHER finite diary every
positive pair at s has the same code below s as that witness,
regardless of which successor class is positive.

We combine the two lemmas to prove that ANY positive pair in P
at s and ANY positive pair in Q at s have IDENTICAL complete
predecessor full two-type codes below s, even when E3 orientations
at s disagree. Thus the V2 parent-profile compatibility across
a sign-rooted shared two-split is a theorem on SOURCE branches.

Important limitation: an actual cross-branch pre-diary would also
have earlier vertices from OTHER branches not present in the
original source. Their Devlin and mixed E/V incidences remain to
be assigned coherently. We prove no such cross-branch completion
or general absorber here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Sign-rooted source flips have matching V2-positive parent
profiles at a shared genuine 2-split s, even if they choose
opposite E3 sides at s. The earlier S2 bit hypotheses are
strictly before s, never including the current split bit. -/
theorem finite_signRooted_positive_twoSplit_parent_codes_agree
    {A P Q : Ordered3Graph Nat} {n : Nat}
    (FP : FiniteDiaryFlip A P n)
    (FQ : FiniteDiaryFlip A Q n)
    (r t s : Nat) (hrt : r < t) (htn : t < n)
    (hr : IsLeaf A r) (ht : IsLeaf A t)
    (hs : IsTwoSplit A s)
    (hReference : P.edge 1 r t ↔ Q.edge 1 r t)
    (hEarlierS2 :
      ∀ q : Nat, IsTwoSplit A q → q < s →
        ∃ a b c d : Nat,
          a < b ∧ c < d ∧ b < n ∧ d < n ∧
          IsLeaf A a ∧ IsLeaf A b ∧
          IsLeaf A c ∧ IsLeaf A d ∧
          q < a ∧ q < c ∧
          A.twoMeetLevel a b c d = q ∧
          (P.edge q a b ↔ Q.edge q a b))
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hc : IsLeaf A c) (hd : IsLeaf A d)
    (hsa : s < a) (hsc : s < c)
    (hMeetA : A.twoMeetLevel a b c d = s)
    (u v x y : Nat)
    (huv : u < v) (hxy : x < y)
    (hu : IsLeaf P u) (hv : IsLeaf P v)
    (hx : IsLeaf Q x) (hy : IsLeaf Q y)
    (hPosP : P.edge s u v)
    (hPosQ : Q.edge s x y) :
    twoCode P s u v = twoCode Q s x y := by
  have hsn : s < n := FP.source_diary.prediary.twoSplit_lt s hs
  have hsP : IsTwoSplit P s :=
    ((FP.role_iff s hs.1 hsn).2.2).mp hs
  have hsQ : IsTwoSplit Q s :=
    ((FQ.role_iff s hs.1 hsn).2.2).mp hs
  have haP : IsLeaf P a :=
    ((FP.role_iff a ha.1 (by omega)).1).mp ha
  have hbP : IsLeaf P b :=
    ((FP.role_iff b hb.1 hbn).1).mp hb
  have hcP : IsLeaf P c :=
    ((FP.role_iff c hc.1 (by omega)).1).mp hc
  have hdP : IsLeaf P d :=
    ((FP.role_iff d hd.1 hdn).1).mp hd
  have haQ : IsLeaf Q a :=
    ((FQ.role_iff a ha.1 (by omega)).1).mp ha
  have hbQ : IsLeaf Q b :=
    ((FQ.role_iff b hb.1 hbn).1).mp hb
  have hcQ : IsLeaf Q c :=
    ((FQ.role_iff c hc.1 (by omega)).1).mp hc
  have hdQ : IsLeaf Q d :=
    ((FQ.role_iff d hd.1 hdn).1).mp hd
  have hMeetP : P.twoMeetLevel a b c d = s :=
    (FP.leaf_twoMeet a b c d hab hcd hbn hdn ha hb hc hd).symm.trans hMeetA
  have hMeetQ : Q.twoMeetLevel a b c d = s :=
    (FQ.leaf_twoMeet a b c d hab hcd hbn hdn ha hb hc hd).symm.trans hMeetA
  have hProfileP : twoCode P s u v = twoCode P s a b :=
    finite_positive_twoSplit_parent_code_eq_witness
      FP.target_diary s a b c d u v
      hsP hab hcd huv haP hbP hcP hdP hu hv
      hsa hsc hMeetP hPosP
  have hProfileQ : twoCode Q s x y = twoCode Q s a b :=
    finite_positive_twoSplit_parent_code_eq_witness
      FQ.target_diary s a b c d x y
      hsQ hab hcd hxy haQ hbQ hcQ hdQ hx hy
      hsa hsc hMeetQ hPosQ
  have hWitnessCode : twoCode P s a b = twoCode Q s a b :=
    finite_signRooted_twoCode_eq_before_cut
      FP FQ r t s hrt htn hr ht
      hReference hEarlierS2 a b hsa hab hbn
  exact hProfileP.trans (hWitnessCode.trans hProfileQ.symm)

end DiaryLeafPriority
end ThreeUniformDiaries
