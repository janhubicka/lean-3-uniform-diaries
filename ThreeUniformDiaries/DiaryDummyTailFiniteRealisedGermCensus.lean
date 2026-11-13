import ThreeUniformDiaries.DiaryDummyTailOldFirstPairGerms
import ThreeUniformDiaries.DiaryFiniteDummyTailRoleCoherence
import ThreeUniformDiaries.DiaryOnePassFiniteSchedule
import Lean.Elab.Tactic.Omega

/-!
# Track B: exact FINITE census of all globally realised dummy-tail germs

Consider the actual verified countable dummy-tail carrier
T=finiteDummyTailCarrier H n bits of a genuine finite diary
edge frame H on [0,n), and an old original cut m<n.

Although realisedOneGerms(T,m) and realisedTwoGerms(T,m) are defined
using existential witnesses among ALL infinitely many tail leaves
and ordered tail pairs, their values have a FINITE explicit census.

Singletons: each actual realised old leaf u in [m,n) contributes
its old singleton germ; every new tail leaf z>=n contributes
EXACTLY the SAME germ as the representative at z=n.

Full ordered pairs: there are precisely THREE forms:
  (1) old-old actual leaf pairs a<b<n;
  (2) old-first/tail-second pairs (a,z), with one representative
      (a,n) for EACH actual old leaf a in [m,n);
  (3) pure tail pairs (a,b), n<=a<b, with the ONE representative
      (n,n+1).

This is an exact ↔ classification of ACTUALLY realised germs, not
a speculative finite coding of an infinite relation. It uses the
already verified old role reflection, tail leaf roles, and literal
singleton/full pair-germ homogeneity of the dummy-tail carrier.

It makes the remaining event-free prefix condition FINITARY in
the finite source diagram and its finite cross orientation bits:
no extra hidden germ types can be introduced by arbitrarily
far tail vertices. Checking COMPATIBILITY of those finitely many
source and tail types is the next, still-open relative extension.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Literal membership in the concrete realised singleton-germ
set, without assumptions that the source graph is a diary. -/
theorem mem_realisedOneGerms_iff_actual_leaf
    (T : Ordered3Graph Nat) (m : Nat) (g : OneGermSpace m) :
    g ∈ realisedOneGerms T m ↔
      ∃ u : Nat, IsLeaf T u ∧ m ≤ u ∧ oneGermCode T m u = g := by
  classical
  simp only [realisedOneGerms, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- Literal membership in the actual realised full ordered-pair
germ set, quantified over true ordered pairs of source leaves. -/
theorem mem_realisedTwoGerms_iff_actual_leafPair
    (T : Ordered3Graph Nat) (m : Nat) (g : TwoGermSpace m) :
    g ∈ realisedTwoGerms T m ↔
      ∃ a b : Nat, IsLeaf T a ∧ IsLeaf T b ∧
        m ≤ a ∧ a < b ∧ twoGermCode T m a b = g := by
  classical
  simp only [realisedTwoGerms, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- Exact singleton-census theorem: each genuinely realised
one-germ below an original cut m<n is either from an ACTUAL
old finite-frame leaf, or is the SINGLE common germ of every
dummy-tail leaf, represented at rank n. -/
theorem finiteDummyTail_realisedOneGerms_oldCut_census
    (H : Ordered3Graph Nat) (n : Nat)
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool) (m : Nat) (hm : m < n)
    (g : OneGermSpace m) :
    let T := finiteDummyTailCarrier H n bits
    g ∈ realisedOneGerms T m ↔
      (∃ u : Nat, m ≤ u ∧ u < n ∧ IsLeaf H u ∧
        oneGermCode T m u = g) ∨
      oneGermCode T m n = g := by
  dsimp only
  let T := finiteDummyTailCarrier H n bits
  constructor
  · intro hReal
    obtain ⟨u,hLeaf,hmu,hCode⟩ :=
      (mem_realisedOneGerms_iff_actual_leaf T m g).mp hReal
    by_cases hun : u < n
    · have hOldLeaf : IsLeaf H u :=
        (finiteDummyTailCarrier_old_leaf_iff
          FH bits u hun).mp hLeaf
      exact Or.inl ⟨u,hmu,hun,hOldLeaf,hCode⟩
    · have hnu : n ≤ u := by omega
      have hEq : oneGermCode T m u = oneGermCode T m n :=
        finiteDummyTail_allTail_oneGermCode_eq
          H n bits m u n hm hnu (le_refl n)
      exact Or.inr (hEq.symm.trans hCode)
  · intro h
    apply (mem_realisedOneGerms_iff_actual_leaf T m g).mpr
    rcases h with ⟨u,hmu,hun,hOldLeaf,hCode⟩ | hTail
    · have hLeaf : IsLeaf T u :=
        (finiteDummyTailCarrier_old_leaf_iff
          FH bits u hun).mpr hOldLeaf
      exact ⟨u,hLeaf,hmu,hCode⟩
    · have hLeaf : IsLeaf T n :=
        finiteDummyTailCarrier_tail_isLeaf FH bits n (le_refl n)
      exact ⟨n,hLeaf,by omega,hTail⟩

/-- Exact full pair-germ census: old-old leaf pairs, old-tail
pairs with ONE representative (a,n) for each old first leaf,
and ONE pure-tail representative (n,n+1) exhaust every
actually realised ordered-pair germ at all old cuts m<n. -/
theorem finiteDummyTail_realisedTwoGerms_oldCut_census
    (H : Ordered3Graph Nat) (n : Nat)
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool) (m : Nat) (hm : m < n)
    (g : TwoGermSpace m) :
    let T := finiteDummyTailCarrier H n bits
    g ∈ realisedTwoGerms T m ↔
      (∃ a b : Nat, m ≤ a ∧ a < b ∧ b < n ∧
        IsLeaf H a ∧ IsLeaf H b ∧
        twoGermCode T m a b = g) ∨
      (∃ a : Nat, m ≤ a ∧ a < n ∧ IsLeaf H a ∧
        twoGermCode T m a n = g) ∨
      twoGermCode T m n (n+1) = g := by
  dsimp only
  let T := finiteDummyTailCarrier H n bits
  constructor
  · intro hReal
    obtain ⟨a,b,hLa,hLb,hma,hab,hCode⟩ :=
      (mem_realisedTwoGerms_iff_actual_leafPair T m g).mp hReal
    by_cases hbn : b < n
    · have han : a < n := by omega
      have hOldA : IsLeaf H a :=
        (finiteDummyTailCarrier_old_leaf_iff
          FH bits a han).mp hLa
      have hOldB : IsLeaf H b :=
        (finiteDummyTailCarrier_old_leaf_iff
          FH bits b hbn).mp hLb
      exact Or.inl ⟨a,b,hma,hab,hbn,hOldA,hOldB,hCode⟩
    · by_cases han : a < n
      · have hnb : n ≤ b := by omega
        have hOldA : IsLeaf H a :=
          (finiteDummyTailCarrier_old_leaf_iff
            FH bits a han).mp hLa
        have hEq : twoGermCode T m a b = twoGermCode T m a n :=
          finiteDummyTail_oldFirst_tailSecond_twoGermCode_eq
            H n bits m a b n hm hma han hnb (le_refl n)
        exact Or.inr (Or.inl
          ⟨a,hma,han,hOldA,hEq.symm.trans hCode⟩)
      · have hna : n ≤ a := by omega
        have hEq : twoGermCode T m a b =
            twoGermCode T m n (n+1) :=
          finiteDummyTail_allTail_twoGermCode_eq
            H n bits m a b n (n+1)
            hm hna hab (le_refl n) (by omega)
        exact Or.inr (Or.inr (hEq.symm.trans hCode))
  · intro h
    apply (mem_realisedTwoGerms_iff_actual_leafPair T m g).mpr
    rcases h with ⟨a,b,hma,hab,hbn,hOldA,hOldB,hCode⟩ |
      ⟨a,hma,han,hOldA,hCode⟩ | hTail
    · have han : a < n := by omega
      have hLa : IsLeaf T a :=
        (finiteDummyTailCarrier_old_leaf_iff
          FH bits a han).mpr hOldA
      have hLb : IsLeaf T b :=
        (finiteDummyTailCarrier_old_leaf_iff
          FH bits b hbn).mpr hOldB
      exact ⟨a,b,hLa,hLb,hma,hab,hCode⟩
    · have hLa : IsLeaf T a :=
        (finiteDummyTailCarrier_old_leaf_iff
          FH bits a han).mpr hOldA
      have hLn : IsLeaf T n :=
        finiteDummyTailCarrier_tail_isLeaf FH bits n (le_refl n)
      exact ⟨a,n,hLa,hLn,hma,han,hCode⟩
    · have hLn : IsLeaf T n :=
        finiteDummyTailCarrier_tail_isLeaf FH bits n (le_refl n)
      have hLn1 : IsLeaf T (n+1) :=
        finiteDummyTailCarrier_tail_isLeaf FH bits (n+1) (by omega)
      exact ⟨n,n+1,hLn,hLn1,by omega,by omega,hTail⟩

end DiaryLeafPriority
end ThreeUniformDiaries
