import ThreeUniformDiaries.DiaryOnePassFullProtectedPrefix
import ThreeUniformDiaries.DiaryFiniteLeafSupportCoversPrefix
import ThreeUniformDiaries.DiaryNoLiteralFiniteFullDiaryEndExtension
import Lean.Elab.Tactic.Omega

/-!
# Track B: genuine finite full relative completion from an event-free global prediary

The full countable one-pass theorem and finite leaf-meet extraction
have now both been verified independently. The precise composition
is useful as a small conditional RELATIVE FINITE COMPLETION theorem:

Given a genuine global RolePrediary H and a numerical cut p whose
ACTUAL one-pass schedule has NO selected events at any old m<p,
there exists a GENUINE finite FULL diary C of length m>p which
preserves the ENTIRE literal source prefix [0,p), including edges,
nonedges, all three marker-defined roles and EVERY exact numerical
capped singleton and full ordered-pair meet. It has a true terminal
leaf after that protected prefix, leaving at least one free tail
vertex.

Proof: perform the already verified full one-pass completion,
whose old prefix remains literal by the no-event condition.
Then use cofinal finite full leaf-meet compression on the countable
RoleDiary, requiring the support to contain [0,max(p+1,4)).
That support's rank enumeration fixes every old protected vertex,
and all exact prefix data survive by literal old-prefix agreement.

The missing positive construction is STILL a global relative
prediary with the required event-free protected cut and the finite
strong flip absorbers. This theorem does not supply that prediary,
nor a bounded-rank selected absorber tower or countable absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A global prediary with no one-pass events below cut p has
a genuine FULL FINITE diary completion retaining exactly the
entire numerical old prefix, with a true final leaf outside p.

This is a CONDITIONAL relative-completion reduction and must
not be confused with a literal end extension of a FULL finite
diary, which is already known to be impossible. -/
theorem exists_finiteFullDiary_retaining_eventFree_prediary_prefix
    {H : Ordered3Graph Nat}
    (PH : RolePrediary H)
    (p : Nat)
    (hNo : OnePassNoEventsBelow H p) :
    ∃ (C : Ordered3Graph Nat) (m : Nat),
      FiniteRoleDiaryBlock C m ∧
      p < m ∧
      LiteralOldPrefixAgreement H C p ∧
      (∀ u : Nat, u < p →
        (IsLeaf H u ↔ IsLeaf C u) ∧
        (IsOneSplit H u ↔ IsOneSplit C u) ∧
        (IsTwoSplit H u ↔ IsTwoSplit C u)) ∧
      (∀ u v : Nat, u < p → v < p →
        H.oneMeetLevel u v = C.oneMeetLevel u v) ∧
      (∀ a b c d : Nat, a < p → b < p → c < p → d < p →
        H.twoMeetLevel a b c d = C.twoMeetLevel a b c d) ∧
      (IsLeaf C (m-1) ∧ p ≤ m-1) := by
  classical
  let K := onePassRawTarget H
  have DK : RoleDiary K := onePassRawTarget_isDiary PH
  let q : Nat := max (p+1) 4
  obtain ⟨L,hLeaves,DC,hKeep⟩ :=
    DK.exists_finite_full_diary_retaining_prefix q
  let S : Finset Nat := finiteLeafMeetSupport K L
  let C : Ordered3Graph Nat := finiteSupportGraph K S
  let m : Nat := S.card
  have hpq : p < q := by dsimp [q]; omega
  have hpm : p < m := (hKeep p hpq).1
  have h3q : 3 < q := by dsimp [q]; omega
  have hFour : 4 ≤ m := by
    have h3m := (hKeep 3 h3q).1
    change 3 < m at h3m
    omega
  have hLast : IsLeaf C (m-1) :=
    DC.last_is_leaf hFour
  have hHK : LiteralOldPrefixAgreement H K p :=
    onePass_noEvents_literalOldPrefix PH p hNo
  have hKC : LiteralOldPrefixAgreement K C p := by
    intro a b c hc
    by_cases hord : a < b ∧ b < c
    · have haQ : a < q := by omega
      have hbQ : b < q := by omega
      have hcQ : c < q := by omega
      have hA := (hKeep a haQ).2
      have hB := (hKeep b hbQ).2
      have hC := (hKeep c hcQ).2
      change finiteSupportIndex S a = a at hA
      change finiteSupportIndex S b = b at hB
      change finiteSupportIndex S c = c at hC
      have hEdge := finiteSupportGraph_edge_iff
        K S a b c hord.1 hord.2 (hKeep c hcQ).1
      rw [hA,hB,hC] at hEdge
      exact hEdge.symm
    · have hKFalse : ¬ K.edge a b c := by
        intro he
        exact hord (DK.edge_ordered a b c he)
      have hCFalse : ¬ C.edge a b c := by
        intro he
        have hs := DC.prediary.frame.edge_support a b c he
        exact hord ⟨hs.1,hs.2.1⟩
      exact iff_of_false hKFalse hCFalse
  have hHC : LiteralOldPrefixAgreement H C p := by
    intro a b c hc
    exact (hHK a b c hc).trans (hKC a b c hc)
  refine ⟨C,m,DC,hpm,hHC,?_,?_,?_,hLast,?_⟩
  · intro u hu
    exact role_iff_of_literalOldPrefix hHC u hu
  · intro u v hu hv
    exact oneMeetLevel_eq_of_literalOldPrefix hHC u v hu hv
  · intro a b c d ha hb hc hd
    exact twoMeetLevel_eq_of_literalOldPrefix hHC
      a b c d ha hb hc hd
  · omega

end DiaryLeafPriority
end ThreeUniformDiaries
