import ThreeUniformDiaries.DiaryMarkerCutOrientation
import ThreeUniformDiaries.DiaryRoleEnvelopeAssembly

/-!
# Shared branches of opposite diary orientation classes

Fix two ordered pairs of source diary leaves a<b and c<d,
with positive LexEarlier(a,b) and negative LexEarlier(c,d).
Let m=a∧b and n=c∧d. The source V/E/S axioms force both
m and n to be one-splits after initial marker cut 3.

Their initial singleton profiles are identical: for any x<y<3,
edge(x,y,m) iff x=0 and y=1, and the same for n.
All diary leaves also share the same singleton type below 3.

The crucial compatibility is that the POSITIVE split branches
b (on the right of m) and c (on the left of n) have the same
auxiliary profile relative to their splits through cut 3:
edge(z,m,b) iff edge(z,n,c) for every z<3.
Both sides hold for z=0; both fail for z=1,2.

Likewise the opposite NEGATIVE branches a and d have equal
mixed auxiliary profiles through cut 3; their z=0 incidences
are both absent. Thus we obtain literal full 2-type equalities

  SameTwoTypeBelow 3 (m,b) (n,c)
  SameTwoTypeBelow 3 (m,a) (n,d).

These are the compatibility conditions on overlapping split and
central-leaf vertices when simultaneously amalgamating the two
native three-tail ATR source pictures. They transfer through any
gappy type-respecting source embedding into the generic graph.

We do NOT yet construct the complete finite glued gadget or
its two ATR embedding codes; that is a separate finite
amalgamation step.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {H : Ordered3Graph Nat}

/-- Every two one-split vertices have identical singleton
types below the initial marker cut 3. -/
theorem oneSplit_sameOneTypeBelow_three (D : RoleDiary H)
    (m n : Nat) (hm : IsOneSplit H m) (hn : IsOneSplit H n) :
    H.SameOneTypeBelow 3 m n := by
  intro x y hxy hy
  have hym : y < m := by
    have h := hm.1
    omega
  have hyn : y < n := by
    have h := hn.1
    omega
  exact (D.oneSplit_incoming m x y hm hxy hym).trans
    (D.oneSplit_incoming n x y hn hxy hyn).symm

/-- Matching edge incidences at the first marker 0 suffice
for equality of mixed split/leaf auxiliary types at cut 3:
V/E forbids every nonzero predecessor-to-one-split/leaf edge. -/
theorem oneSplit_leafAux_eqBelow_three_of_zero_bit (D : RoleDiary H)
    (m n u v : Nat)
    (hm : IsOneSplit H m) (hn : IsOneSplit H n)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m < u) (hnv : n < v)
    (hzero : H.edge 0 m u ↔ H.edge 0 n v) :
    H.SameAuxTypeBelow 3 m u n v := by
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    exact hzero
  · have hzm : z < m := by
      have hm3 := hm.1
      omega
    have hzn : z < n := by
      have hn3 := hn.1
      omega
    have hNoM : ¬ H.edge z m u :=
      D.splitEdgeShape.oneSplit_earlier_only_zero
        m u z hm hu hzm hz0
    have hNoN : ¬ H.edge z n v :=
      D.splitEdgeShape.oneSplit_earlier_only_zero
        n v z hn hv hzn hz0
    exact iff_of_false hNoM hNoN

/-- Opposite lexicographic orientation classes have compatible
positive and negative mixed split/leaf branch profiles at
marker cut 3. Both full 2-types here are actual edge-derived
types, not additional coherence axioms. -/
theorem oppositeLex_same_branch_profiles_below_three (D : RoleDiary H)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hplus : LexEarlier H a b)
    (hminus : ¬ LexEarlier H c d) :
    let m := H.oneMeetLevel a b
    let n := H.oneMeetLevel c d
    H.SameTwoTypeBelow 3 m b n c ∧
    H.SameTwoTypeBelow 3 m a n d := by
  let m := H.oneMeetLevel a b
  let n := H.oneMeetLevel c d
  have hm : IsOneSplit H m :=
    D.singleton_meets a b ha hb (ne_of_lt hab)
  have hn : IsOneSplit H n :=
    D.singleton_meets c d hc hd (ne_of_lt hcd)
  have hma : m < a :=
    D.leaf_meet_lt_first a b ha hb (ne_of_lt hab)
  have hnc : n < c :=
    D.leaf_meet_lt_first c d hc hd (ne_of_lt hcd)
  have hmb : m < b := lt_trans hma hab
  have hnd : n < d := lt_trans hnc hcd
  have hRightM : H.edge 0 m b :=
    (D.lexEarlier_iff_right_split_marker
      m a b hm ha hb hab hma rfl).mp hplus
  have hLeftN : H.edge 0 n c := by
    have hmark : H.edge 2 c d :=
      (D.leaf_marker_two c d hcd hc hd).mpr hminus
    exact (D.oneSplit_left_right_marker
      n c d hn hc hd hcd hnc rfl).1.mpr hmark
  have hNoLeftM : ¬ H.edge 0 m a := by
    intro he
    have hmark : H.edge 2 a b :=
      (D.oneSplit_left_right_marker
        m a b hm ha hb hab hma rfl).1.mp he
    exact ((D.leaf_marker_two a b hab ha hb).mp hmark) hplus
  have hNoRightN : ¬ H.edge 0 n d := by
    intro he
    exact hminus
      ((D.lexEarlier_iff_right_split_marker
        n c d hn hc hd hcd hnc rfl).mpr he)
  have hSplit : H.SameOneTypeBelow 3 m n :=
    D.oneSplit_sameOneTypeBelow_three m n hm hn
  have hPositive : H.SameTwoTypeBelow 3 m b n c := by
    refine ⟨hSplit, D.leaf_sameOneTypeBelow_three b c hb hc, ?_⟩
    apply D.oneSplit_leafAux_eqBelow_three_of_zero_bit
      m n b c hm hn hb hc hmb hnc
    exact ⟨fun _ => hLeftN, fun _ => hRightM⟩
  have hNegative : H.SameTwoTypeBelow 3 m a n d := by
    refine ⟨hSplit, D.leaf_sameOneTypeBelow_three a d ha hd, ?_⟩
    apply D.oneSplit_leafAux_eqBelow_three_of_zero_bit
      m n a d hm hn ha hd hma hnd
    exact iff_of_false hNoLeftM hNoRightN
  exact ⟨hPositive, hNegative⟩

/-- The same two overlap equalities hold through the FULL generic
prefix ending at the image of marker cut 3. The source embedding
may skip arbitrary levels; type-respecting reflection handles
all intervening target vertices exactly. -/
theorem oppositeLex_same_branch_profiles_in_generic (D : RoleDiary H)
    (G : GenericEnumerated3Graph)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hplus : LexEarlier H a b)
    (hminus : ¬ LexEarlier H c d) :
    let m := H.oneMeetLevel a b
    let n := H.oneMeetLevel c d
    G.graph.SameTwoTypeBelow (ψ 3)
      (ψ m) (ψ b) (ψ n) (ψ c) ∧
    G.graph.SameTwoTypeBelow (ψ 3)
      (ψ m) (ψ a) (ψ n) (ψ d) := by
  let m := H.oneMeetLevel a b
  let n := H.oneMeetLevel c d
  have hm : IsOneSplit H m :=
    D.singleton_meets a b ha hb (ne_of_lt hab)
  have hn : IsOneSplit H n :=
    D.singleton_meets c d hc hd (ne_of_lt hcd)
  have hma : m < a :=
    D.leaf_meet_lt_first a b ha hb (ne_of_lt hab)
  have hnc : n < c :=
    D.leaf_meet_lt_first c d hc hd (ne_of_lt hcd)
  have hmb : m < b := lt_trans hma hab
  have hnd : n < d := lt_trans hnc hcd
  have h3m : 3 ≤ m := hm.1
  have h3n : 3 ≤ n := hn.1
  obtain ⟨hPos, hNeg⟩ :=
    D.oppositeLex_same_branch_profiles_below_three
      a b c d hab hcd ha hb hc hd hplus hminus
  constructor
  · exact (hψ.two 3 m b n c h3m hmb h3n hnc).mp hPos
  · exact (hψ.two 3 m a n d h3m hma h3n hnd).mp hNeg

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
