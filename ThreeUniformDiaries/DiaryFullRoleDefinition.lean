import ThreeUniformDiaries.DiaryPointedProfileFromRoles
import ThreeUniformDiaries.DiaryEdgeShapeWitness

/-!
# The manuscript's role-based diary as one complete finite-language interface

This records the (V), (E), and (S) clauses, with roles encoded by the
actual marker edges, not by independent unary predicates. Edges are
represented only on increasing triples. The two leaf-order marker
clauses use the manuscript's definition of lexicographic comparison
from singleton and full pair-type meets.

The orientation is important: for leaves a < b split at m, the
lexicographic definition reads the edge (0,m,b), NOT (0,m,a).
Thus the left split/leaf edge corresponds to marker 2 and the right
split/leaf edge to marker 1. This corrects the reversed correspondences
in the old envelope proof.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Lexicographic precedence in the sense of the manuscript.
For a non-capped singleton meet m, the deciding edge is between
the full meet of pairs (m,a),(m,b), the split m, and the second
vertex b. -/
def LexEarlier (H : Ordered3Graph Nat) (a b : Nat) : Prop :=
  (a < b ∧ H.oneMeetLevel a b = a) ∨
  (let m := H.oneMeetLevel a b
   m < min a b ∧ H.edge (H.twoMeetLevel m a m b) m b)

/-- Exactly the five allowed forms (E1)--(E5) of an increasing
edge from the manuscript's role-based definition. -/
def PermittedDiaryEdge (H : Ordered3Graph Nat) (x y z : Nat) : Prop :=
  (x = 0 ∧ (y = 1 ∨ y = 2) ∧ 3 ≤ z) ∨
  (x = 0 ∧ IsOneSplit H y ∧ IsLeaf H z) ∨
  (IsTwoSplit H x ∧ IsLeaf H y ∧ IsLeaf H z) ∨
  ((x = 1 ∨ x = 2) ∧ IsLeaf H y ∧ IsLeaf H z) ∨
  (IsLeaf H x ∧ IsLeaf H y ∧ IsLeaf H z)

/-- Faithful role-based diary conditions. The witness and coherence
clauses are the two (V1)/(V2) split axioms. S1/S2 are exactly the
leaf-meet conditions. The E clause classifies all increasing edges.
The V leaf clauses are the two lexicographic marker equivalences.

The class is stated for countable enumerations on Nat; finite
diaries can be represented by restricting all clauses to a
finite initial segment, which is a separate finite interface. -/
structure RoleDiary (H : Ordered3Graph Nat) : Prop where
  role_valid :
    ∀ v, 3 ≤ v → IsLeaf H v ∨ IsOneSplit H v ∨ IsTwoSplit H v
  one_split_coherent :
    ∀ m a b, IsOneSplit H m → IsLeaf H a → IsLeaf H b →
      H.edge 0 m a → H.edge 0 m b →
      H.SameOneTypeBelow m a b
  one_split_witness :
    ∀ m, IsOneSplit H m →
      ∃ a b, IsLeaf H a ∧ IsLeaf H b ∧
        m < a ∧ m < b ∧ H.oneMeetLevel a b = m
  two_split_coherent :
    ∀ m a b c d, IsTwoSplit H m →
      a < b → c < d →
      IsLeaf H a → IsLeaf H b → IsLeaf H c → IsLeaf H d →
      H.edge m a b → H.edge m c d →
      H.SameTwoTypeBelow m a b c d
  two_split_witness :
    ∀ m, IsTwoSplit H m →
      ∃ a b c d, a < b ∧ c < d ∧
        IsLeaf H a ∧ IsLeaf H b ∧ IsLeaf H c ∧ IsLeaf H d ∧
        m < a ∧ m < c ∧ H.twoMeetLevel a b c d = m
  leaf_marker_one :
    ∀ a b, a < b → IsLeaf H a → IsLeaf H b →
      (H.edge 1 a b ↔ LexEarlier H a b)
  leaf_marker_two :
    ∀ a b, a < b → IsLeaf H a → IsLeaf H b →
      (H.edge 2 a b ↔ ¬ LexEarlier H a b)
  edge_ordered :
    ∀ x y z, H.edge x y z → x < y ∧ y < z
  permitted_edge :
    ∀ x y z, H.edge x y z → PermittedDiaryEdge H x y z
  singleton_meets :
    ∀ a b, IsLeaf H a → IsLeaf H b → a ≠ b →
      IsOneSplit H (H.oneMeetLevel a b)
  pair_meets :
    ∀ a b c d, a < b → c < d →
      IsLeaf H a → IsLeaf H b → IsLeaf H c → IsLeaf H d →
      H.twoMeetLevel a b c d = min a c ∨
      H.twoMeetLevel a b c d = 1 ∨
      IsTwoSplit H (H.twoMeetLevel a b c d)

namespace RoleDiary

variable {H : Ordered3Graph Nat} (D : RoleDiary H)

theorem roleMeets : RoleDiaryMeets H :=
  ⟨D.singleton_meets, D.pair_meets⟩

private theorem oneSplit_not_leaf
    {m : Nat} (hm : IsOneSplit H m) : ¬ IsLeaf H m := by
  intro hleaf
  exact hleaf.2.1 hm.2.1

private theorem oneSplit_not_twoSplit
    {m : Nat} (hm : IsOneSplit H m) : ¬ IsTwoSplit H m := by
  intro htwo
  exact htwo.2.1 hm.2.1

/-- The edge-shape lemma used by ATR follows from the manuscript's
five permitted edge forms and the Devlin marker equivalences. -/
theorem splitEdgeShape : SplitEdgeShape H := by
  constructor
  · intro m a z hm ha hzm hz0 he
    rcases D.permitted_edge z m a he with hrole | hsplit | htwo | hdevlin | hnormal
    · exact hz0 hrole.1
    · exact hz0 hsplit.1
    · exact (D.oneSplit_not_leaf hm) htwo.2.1
    · exact (D.oneSplit_not_leaf hm) hdevlin.2.1
    · exact (D.oneSplit_not_leaf hm) hnormal.2.1
  · intro a b hab ha hb
    classical
    by_cases hlex : LexEarlier H a b
    · exact Or.inl ((D.leaf_marker_one a b hab ha hb).mpr hlex)
    · exact Or.inr ((D.leaf_marker_two a b hab ha hb).mpr hlex)

/-- Every 1-split has precisely the incoming marker-one profile. -/
theorem oneSplit_incoming
    (m x y : Nat) (hm : IsOneSplit H m)
    (hxy : x < y) (hym : y < m) :
    (H.edge x y m ↔ (x = 0 ∧ y = 1)) := by
  constructor
  · intro he
    rcases D.permitted_edge x y m he with hrole | hsplit | htwo | hdevlin | hnormal
    · rcases hrole with ⟨hx, hy, _⟩
      refine ⟨hx, ?_⟩
      rcases hy with hy | hy
      · exact hy
      · have hforbidden : H.edge 0 2 m := by
          simpa only [hx, hy] using he
        exact (hm.2.2 hforbidden).elim
    · exact False.elim ((D.oneSplit_not_leaf hm) hsplit.2.2)
    · exact False.elim ((D.oneSplit_not_leaf hm) htwo.2.2)
    · exact False.elim ((D.oneSplit_not_leaf hm) hdevlin.2.2)
    · exact False.elim ((D.oneSplit_not_leaf hm) hnormal.2.2)
  · rintro ⟨rfl, rfl⟩
    exact hm.2.1

/-- No permitted diary edge has a 1-split as its first vertex and
two leaves as its second and third vertices. -/
theorem oneSplit_no_terminal
    (m a b : Nat) (hm : IsOneSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hab : a < b) (hma : m < a) :
    ¬ H.edge m a b := by
  intro he
  rcases D.permitted_edge m a b he with hrole | hsplit | htwo | hdevlin | hnormal
  · have hbound := hm.1
    omega
  · have hbound := hm.1
    omega
  · exact (D.oneSplit_not_twoSplit hm) htwo.1
  · have hbound := hm.1
    rcases hdevlin.1 with h | h <;> omega
  · exact (D.oneSplit_not_leaf hm) hnormal.1

/-- The full pair meet of (m,a) and (m,b) is zero, provided m
is exactly the leaf singleton meet; this is the lexicographic
orientation witness and not a special axiom. -/
theorem oneSplit_mixed_pair_meet_zero
    (m a b : Nat) (hm : IsOneSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hab : a < b) (hma : m < a)
    (hmeet : H.oneMeetLevel a b = m) :
    H.twoMeetLevel m a m b = 0 := by
  have hmb : m < b := lt_trans hma hab
  have haux := oneSplit_pointed_aux_bounds H D.splitEdgeShape
    m a b hab ha hb hm hmeet hma hmb
  rw [H.twoMeetLevel_eq_min m a m b hma hmb, haux.1]
  simp

/-- For a<b, the manuscript's lexicographic comparison is
equivalent to the *right* split/leaf edge (0,m,b). -/
theorem lexEarlier_iff_right_split_marker
    (m a b : Nat) (hm : IsOneSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hab : a < b) (hma : m < a)
    (hmeet : H.oneMeetLevel a b = m) :
    LexEarlier H a b ↔ H.edge 0 m b := by
  have htwo := D.oneSplit_mixed_pair_meet_zero
    m a b hm ha hb hab hma hmeet
  change (a < b ∧ H.oneMeetLevel a b = a) ∨
    (H.oneMeetLevel a b < min a b ∧
      H.edge
        (H.twoMeetLevel (H.oneMeetLevel a b) a (H.oneMeetLevel a b) b)
        (H.oneMeetLevel a b) b) ↔ H.edge 0 m b
  constructor
  · rintro (⟨_, hcap⟩ | ⟨_, he⟩)
    · rw [hmeet] at hcap
      omega
    · simpa only [hmeet, htwo] using he
  · intro he
    exact Or.inr ⟨by omega, by simpa only [hmeet, htwo] using he⟩

/-- The actual (E/V) marker pair identities, correctly oriented:
edge(0,m,a) iff marker 2 and edge(0,m,b) iff marker 1. -/
theorem oneSplit_left_right_marker
    (m a b : Nat) (hm : IsOneSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hab : a < b) (hma : m < a)
    (hmeet : H.oneMeetLevel a b = m) :
    (H.edge 0 m a ↔ H.edge 2 a b) ∧
    (H.edge 0 m b ↔ H.edge 1 a b) := by
  have hmb : m < b := lt_trans hma hab
  have hbranch :=
    oneSplit_branch_zero H D.splitEdgeShape m a b ha hb hm hmeet hma hmb
  have hcomplement : H.edge 0 m a ↔ ¬ H.edge 0 m b := by
    rcases hbranch with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · tauto
    · tauto
  have hlex :=
    D.lexEarlier_iff_right_split_marker m a b hm ha hb hab hma hmeet
  constructor
  · exact hcomplement.trans
      ((not_congr hlex.symm).trans
        (D.leaf_marker_two a b hab ha hb).symm)
  · exact hlex.symm.trans
      (D.leaf_marker_one a b hab ha hb).symm

/-- All pointed role-profile assumptions are consequences of the
single complete diary definition. No independent branch-marker
axiom is used. -/
theorem pointedEnvelopeAxioms : RolePointedEnvelopeAxioms H := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m x y hm hxy hym
    exact D.oneSplit_incoming m x y hm hxy hym
  · exact D.splitEdgeShape.oneSplit_earlier_only_zero
  · intro m a b hm ha hb hab hmeet
    have hma : m < a := by
      have hle : m ≤ a := by
        rw [← hmeet]
        exact (H.oneMeetLevel_le_min a b).trans (min_le_left _ _)
      have hne : m ≠ a := by
        intro h
        subst m
        exact (D.oneSplit_not_leaf hm) ha
      omega
    exact (D.oneSplit_left_right_marker m a b hm ha hb hab hma hmeet).1
  · intro m a b hm ha hb hab hmeet
    have hma : m < a := by
      have hle : m ≤ a := by
        rw [← hmeet]
        exact (H.oneMeetLevel_le_min a b).trans (min_le_left _ _)
      have hne : m ≠ a := by
        intro h
        subst m
        exact (D.oneSplit_not_leaf hm) ha
      omega
    exact (D.oneSplit_left_right_marker m a b hm ha hb hab hma hmeet).2
  · intro m a b hm ha hb hab hma
    exact D.oneSplit_no_terminal m a b hm ha hb hab hma

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
