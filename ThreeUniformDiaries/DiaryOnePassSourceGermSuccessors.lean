import ThreeUniformDiaries.DiaryOnePassGermSignatures
import ThreeUniformDiaries.DiaryPrediaryDefinition

/-!
# Source normal/terminal germs are exactly successor-cut types

The corrected one-pass construction separates the ORIGINAL m-type
parent classes into normal and terminal germs. To turn the verified
target event-class partition into the global type-transport step, we
must verify that those source germ labels represent EXACTLY the
original source types through the next cut m+1.

The key difficulty is terminal germs. When m itself is an original
leaf, the V3 marker on each ordered pair (m,u), u>m, prevents
singleton type agreement between m and a later leaf through m+1.
For full ordered-pair types, the analogous terminal-pair calculation
also uses that increasing hyperedges cannot have a repeated vertex.

We prove both arities for actual source leaves under pre-diary V/E,
without assuming completed-diary S1 or S2, and including every
normal-versus-terminal case.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

variable {H : Ordered3Graph Nat}

/-- At an original LEAF cut m, equality of actual singleton
normal/terminal germ signatures is EXACTLY equality of original
singleton types through m+1, including terminal-vs-normal cases. -/
theorem oneGerm_eq_iff_nextOneType_of_source_leaf
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsLeaf H m) (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v) :
    (oneGermCode H m u = oneGermCode H m v) ↔
      H.SameOneTypeBelow (m + 1) u v := by
  classical
  by_cases hum : u = m
  · by_cases hvm : v = m
    · subst u
      subst v
      constructor
      · intro _
        intro a b hab hb
        rfl
      · intro _
        rfl
    · subst u
      have hmv' : m < v := by omega
      constructor
      · intro hg
        exact False.elim
          ((oneGerm_terminal_ne_normal H m v hvm) hg)
      · intro hnext
        exact False.elim
          ((P.leaf_pair_disagrees_at_first_next_cut
            m v hmv' hm hv) hnext)
  · by_cases hvm : v = m
    · subst v
      have hmu' : m < u := by omega
      constructor
      · intro hg
        exact False.elim
          ((oneGerm_terminal_ne_normal H m u hum) hg.symm)
      · intro hnext
        have hreverse : H.SameOneTypeBelow (m + 1) m u := by
          intro a b hab hb
          exact (hnext hab hb).symm
        exact False.elim
          ((P.leaf_pair_disagrees_at_first_next_cut
            m u hmu' hm hu) hreverse)
    · have hn := oneGerm_eq_iff_normal H m u v hum hvm
      constructor
      · intro hg
        exact (hn.mp hg).2
      · intro hnext
        apply hn.mpr
        refine ⟨?_, hnext⟩
        intro a b hab hb
        exact hnext hab (by omega)

/-- The same statement in the finite Boolean singleton-code API
used by the one-pass scheduler and the target partition lemmas. -/
theorem oneGerm_eq_iff_nextOneCode_of_source_leaf
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsLeaf H m) (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v) :
    (oneGermCode H m u = oneGermCode H m v) ↔
      (oneCode H (m + 1) u = oneCode H (m + 1) v) := by
  exact (oneGerm_eq_iff_nextOneType_of_source_leaf
    P m u v hm hu hv hmu hmv).trans
    (oneCode_eq_iff_sameOneType H (m + 1) u v).symm

/-- For capped terminal pairs (m,u) and (m,v), the complete
source pair type at m+1 is precisely the later leaf's next
singleton type: the extra auxiliary bit at x=m is always zero. -/
theorem terminalTwoType_succ_iff_nextOneType
    (P : RolePrediary H) (m u v : Nat) :
    H.SameTwoTypeBelow (m + 1) m u m v ↔
      H.SameOneTypeBelow (m + 1) u v := by
  constructor
  · intro h
    exact h.2.1
  · intro hnext
    refine ⟨?_, hnext, ?_⟩
    · intro a b hab hb
      rfl
    · intro x hx
      by_cases hxm : x < m
      · exact hnext hxm (by omega)
      · have heq : x = m := by omega
        subst x
        have hnu : ¬ H.edge m m u := by
          intro he
          exact (lt_irrefl m) (P.edge_ordered m m u he).1
        have hnv : ¬ H.edge m m v := by
          intro he
          exact (lt_irrefl m) (P.edge_ordered m m v he).1
        exact iff_of_false hnu hnv

/-- Terminal full pair-germ equality is exactly original full
pair-type equality through the next cut, not merely sufficient. -/
theorem terminalTwoGerm_eq_iff_nextTwoType
    (P : RolePrediary H) (m u v : Nat) :
    (twoGermCode H m m u = twoGermCode H m m v) ↔
      H.SameTwoTypeBelow (m + 1) m u m v := by
  exact (twoGerm_terminal_eq_iff_parent H m u v).trans
    ((H.terminal_pair_type_iff_next_singleton m u v).trans
      (terminalTwoType_succ_iff_nextOneType P m u v).symm)

/-- For an original LEAF cut, equality of actual full pair
normal/terminal germ signatures is EXACTLY equality of the
source complete ordered pair type through m+1. -/
theorem twoGerm_eq_iff_nextTwoType_of_source_leaf
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsLeaf H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hma : m ≤ a) (hab : a < b)
    (hmc : m ≤ c) (hcd : c < d) :
    (twoGermCode H m a b = twoGermCode H m c d) ↔
      H.SameTwoTypeBelow (m + 1) a b c d := by
  classical
  by_cases ham : a = m
  · by_cases hcm : c = m
    · subst a
      subst c
      exact terminalTwoGerm_eq_iff_nextTwoType P m b d
    · subst a
      have hmc' : m < c := by omega
      constructor
      · intro hg
        exact False.elim
          ((twoGerm_terminal_ne_normal H m b c d hcm) hg)
      · intro hnext
        exact False.elim
          ((P.leaf_pair_disagrees_at_first_next_cut
            m c hmc' hm hc) hnext.1)
  · by_cases hcm : c = m
    · subst c
      have hma' : m < a := by omega
      constructor
      · intro hg
        exact False.elim
          ((twoGerm_terminal_ne_normal H m d a b ham) hg.symm)
      · intro hnext
        have hreverse : H.SameOneTypeBelow (m + 1) m a := by
          intro x y hxy hy
          exact (hnext.1 hxy hy).symm
        exact False.elim
          ((P.leaf_pair_disagrees_at_first_next_cut
            m a hma' hm ha) hreverse)
    · have hn := twoGerm_eq_iff_normal H m a b c d ham hcm
      constructor
      · intro hg
        exact (hn.mp hg).2
      · intro hnext
        apply hn.mpr
        refine ⟨?_, hnext⟩
        refine ⟨?_, ?_, ?_⟩
        · intro x y hxy hy
          exact hnext.1 hxy (by omega)
        · intro x y hxy hy
          exact hnext.2.1 hxy (by omega)
        · intro x hx
          exact hnext.2.2 (by omega)

/-- Finite source full pair-code version, including capped
terminal germs and all mixed terminal/normal cases. -/
theorem twoGerm_eq_iff_nextTwoCode_of_source_leaf
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsLeaf H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hma : m ≤ a) (hab : a < b)
    (hmc : m ≤ c) (hcd : c < d) :
    (twoGermCode H m a b = twoGermCode H m c d) ↔
      (twoCode H (m + 1) a b = twoCode H (m + 1) c d) := by
  exact (twoGerm_eq_iff_nextTwoType_of_source_leaf
    P m a b c d hm ha hb hc hd hma hab hmc hcd).trans
    (twoCode_eq_iff_sameTwoType H (m + 1) a b c d).symm

end DiaryLeafPriority
end ThreeUniformDiaries
