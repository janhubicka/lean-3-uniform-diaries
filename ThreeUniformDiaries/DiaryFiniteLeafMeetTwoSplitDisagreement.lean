import ThreeUniformDiaries.DiaryFiniteLeafMeetPrefixCompression
import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Retained two-split auxiliary disagreement under finite compression

A compressed finite induced support may omit type-test coordinates,
so forward type transport only yields a LOWER bound for a meet.
At a genuine source two-split m, however, E1--E5 make every
singleton test with middle coordinate m false: m is neither a
one-split nor a leaf. Consequently an exact source full pair meet
at m is witnessed by differing auxiliary bits (m,a,b)/(m,c,d).

If the source split m and the compared source pairs are retained
by a finite increasing support, this disagreement survives in
the compressed graph literally at the new index k for m.
Together with the forward prefix agreement theorem this proves
the EXACT full ordered-pair meet at k.

This is the proper 2-split case of finite diary extraction.
Marker-one and capped full-pair cases are separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {S : Finset Nat}

/-- E1--E5 prohibit *any* edge with middle coordinate a genuine
two-split: E2 asks for a one-split, E3--E5 ask for a leaf, and
E1 has middle coordinate 1 or 2. -/
theorem E_twoSplit_no_incoming_middle
    (hE : ∀ x y z : Nat, G.edge x y z →
      PermittedDiaryEdge G x y z)
    (m x z : Nat) (hm : IsTwoSplit G m) :
    ¬ G.edge x m z := by
  have hm3 : 3 ≤ m := hm.1
  have hmNotLeaf : ¬ IsLeaf G m := by
    intro hl
    exact hl.2.2 hm.2.2
  have hmNotOne : ¬ IsOneSplit G m := by
    intro hOne
    exact hm.2.1 hOne.2.1
  intro he
  rcases hE x m z he with hMarker | hOne | hTwo | hDevlin | hNormal
  · rcases hMarker.2.1 with h | h <;> omega
  · exact hmNotOne hOne.2.1
  · exact hmNotLeaf hTwo.2.1
  · exact hmNotLeaf hDevlin.2.1
  · exact hmNotLeaf hNormal.2.1

/-- At a strict full pair-type meet located at a two-split, the
first disagreement MUST be the pair incidence at that split.
No singleton coordinate can differ at its middle level. -/
theorem E_twoSplit_pair_aux_distinguishes
    (hE : ∀ x y z : Nat, G.edge x y z →
      PermittedDiaryEdge G x y z)
    (m a b c d : Nat)
    (hm : IsTwoSplit G m)
    (hma : m < a) (hmc : m < c)
    (hMeet : G.twoMeetLevel a b c d = m) :
    ¬ (G.edge m a b ↔ G.edge m c d) := by
  classical
  have hSourceAt : G.SameTwoTypeBelow m a b c d := by
    rw [← hMeet]
    exact G.twoMeetLevel_agree a b c d
  have hSourceNextFail : ¬ G.SameTwoTypeBelow (m + 1) a b c d := by
    intro hNext
    have hCap : m + 1 ≤ min a c := by omega
    have hTooLarge : m + 1 ≤ G.twoMeetLevel a b c d :=
      Nat.le_findGreatest hCap hNext
    omega
  intro hSame
  apply hSourceNextFail
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    by_cases hym : y < m
    · exact hSourceAt.1 hxy hym
    · have heq : y = m := by omega
      subst y
      exact iff_of_false
        (E_twoSplit_no_incoming_middle hE m x a hm)
        (E_twoSplit_no_incoming_middle hE m x c hm)
  · intro x y hxy hy
    by_cases hym : y < m
    · exact hSourceAt.2.1 hxy hym
    · have heq : y = m := by omega
      subst y
      exact iff_of_false
        (E_twoSplit_no_incoming_middle hE m x b hm)
        (E_twoSplit_no_incoming_middle hE m x d hm)
  · intro x hx
    by_cases hxm : x < m
    · exact hSourceAt.2.2 hxm
    · have heq : x = m := by omega
      subst x
      exact hSame

/-- EXACT compressed full meet at a retained genuine two-split.
The input source pairs are genuinely increasing, with their
first coordinates after the split; the support need not contain
any other ambient old type-test coordinates. -/
theorem finiteSupportGraph_twoMeet_exact_at_retained_twoSplit
    (D : RoleDiary G)
    (i j p q k : Nat)
    (hi : i < S.card) (hj : j < S.card)
    (hp : p < S.card) (hq : q < S.card)
    (hk : k < S.card)
    (hij : i < j) (hpq : p < q)
    (hki : k < i) (hkp : k < p)
    (hSplit : IsTwoSplit G (finiteSupportIndex S k))
    (hMeet :
      G.twoMeetLevel
        (finiteSupportIndex S i) (finiteSupportIndex S j)
        (finiteSupportIndex S p) (finiteSupportIndex S q) =
          finiteSupportIndex S k) :
    (finiteSupportGraph G S).twoMeetLevel i j p q = k := by
  classical
  let H := finiteSupportGraph G S
  let m := finiteSupportIndex S k
  have hOldKi := finiteSupportIndex_strictMono S k i hki hi
  have hOldKp := finiteSupportIndex_strictMono S k p hkp hp
  have hDifferent :
      ¬ (G.edge m (finiteSupportIndex S i) (finiteSupportIndex S j) ↔
         G.edge m (finiteSupportIndex S p) (finiteSupportIndex S q)) :=
    E_twoSplit_pair_aux_distinguishes
      D.permitted_edge m
      (finiteSupportIndex S i) (finiteSupportIndex S j)
      (finiteSupportIndex S p) (finiteSupportIndex S q)
      hSplit hOldKi hOldKp hMeet
  have hSourceAt :
      G.SameTwoTypeBelow (finiteSupportIndex S k)
        (finiteSupportIndex S i) (finiteSupportIndex S j)
        (finiteSupportIndex S p) (finiteSupportIndex S q) := by
    rw [← hMeet]
    exact G.twoMeetLevel_agree
      (finiteSupportIndex S i) (finiteSupportIndex S j)
      (finiteSupportIndex S p) (finiteSupportIndex S q)
  have hTargetAt : H.SameTwoTypeBelow k i j p q :=
    finiteSupportGraph_twoType_of_original
      (G := G) (S := S) k i j p q
      hk hi hj hp hq hij hpq hki.le hkp.le hSourceAt
  have hLower : k ≤ H.twoMeetLevel i j p q :=
    Nat.le_findGreatest (by omega) hTargetAt
  have hTargetDifferent :
      ¬ (H.edge k i j ↔ H.edge k p q) := by
    intro heq
    have hAB := finiteSupportGraph_edge_iff G S k i j hki hij hj
    have hCD := finiteSupportGraph_edge_iff G S k p q hkp hpq hq
    exact hDifferent (hAB.symm.trans (heq.trans hCD))
  have hUpper : H.twoMeetLevel i j p q ≤ k := by
    by_contra hn
    have hklt : k < H.twoMeetLevel i j p q := by omega
    have hAgree := H.twoMeetLevel_agree i j p q
    exact hTargetDifferent (hAgree.2.2 hklt)
  change H.twoMeetLevel i j p q = k
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
