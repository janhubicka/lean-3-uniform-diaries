import ThreeUniformDiaries.DiaryPrediaryDefinition

/-!
# One-split and two-split successor-cut lemmas from V/E alone

The one-pass construction starts with a PRE-diary: V1/V2/V3 and E
hold, but S1/S2 need not. The existing genuine RoleDiary
successor-cut lemmas are too strong as an interface because they
require the full completed diary predicate.

This file extracts precisely their V/E-only core:
* at an old 1-split m, the only possible new singleton test
  at column m has first coordinate 0;
* at an old 2-split m, no singleton test has middle coordinate m;
* consequently, successor singleton/full pair types are obtained
  by adding just their one permitted old split-incidence bit.

No assumption on singleton/pair meets S1/S2 is made.
These lemmas provide the exact original-split cases required by
the static one-pass finite-prefix transport induction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RolePrediary

variable {H : Ordered3Graph Nat}

/-- E permits a 1-split m in the middle position only with
first coordinate zero, independently of S1/S2. -/
theorem oneSplit_no_nonzero_middle
    (P : RolePrediary H) (m z u : Nat)
    (hm : IsOneSplit H m) (hz : z ≠ 0) :
    ¬ H.edge z m u := by
  have hNotLeaf : ¬ IsLeaf H m := by
    intro h
    exact h.2.1 hm.2.1
  intro he
  rcases P.permitted_edge z m u he with
      hRole | hSplit | hTwo | hDevlin | hNormal
  · exact hz hRole.1
  · exact hz hSplit.1
  · exact hNotLeaf hTwo.2.1
  · exact hNotLeaf hDevlin.2.1
  · exact hNotLeaf hNormal.2.1

/-- Moving a singleton-type cut through an OLD 1-split adds
only the marker incidence (0,m,u); all other new tests vanish. -/
theorem oneSplit_sameOneType_succ_iff
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsOneSplit H m) :
    H.SameOneTypeBelow (m+1) u v ↔
      H.SameOneTypeBelow m u v ∧
      (H.edge 0 m u ↔ H.edge 0 m v) := by
  rw [H.sameOneTypeBelow_succ_iff m u v]
  constructor
  · rintro ⟨hBefore,hColumn⟩
    have h0 : 0 < m := by have h := hm.1; omega
    exact ⟨hBefore,hColumn 0 h0⟩
  · rintro ⟨hBefore,hBit⟩
    constructor
    · exact hBefore
    · intro z hz
      by_cases hz0 : z = 0
      · subst z
        exact hBit
      · exact iff_of_false
          (P.oneSplit_no_nonzero_middle m z u hm hz0)
          (P.oneSplit_no_nonzero_middle m z v hm hz0)

/-- Positive leaves at an OLD 1-split are in the same next-cut
singleton child: V1 gives the old prefix, E the sole new bit. -/
theorem oneSplit_positive_next_type
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsOneSplit H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (heU : H.edge 0 m u) (heV : H.edge 0 m v) :
    H.SameOneTypeBelow (m+1) u v := by
  apply (P.oneSplit_sameOneType_succ_iff m u v hm).mpr
  exact ⟨P.one_split_coherent m u v hm hu hv heU heV,
    ⟨fun _ => heV, fun _ => heU⟩⟩

/-- Under E, an OLD 2-split never occurs as the middle vertex
of an increasing edge, with no S1/S2 assumptions. -/
theorem twoSplit_no_middle
    (P : RolePrediary H) (m z u : Nat)
    (hm : IsTwoSplit H m) :
    ¬ H.edge z m u := by
  have hNotLeaf : ¬ IsLeaf H m := by
    intro h
    exact h.2.2 hm.2.2
  have hNotOne : ¬ IsOneSplit H m := by
    intro h
    exact hm.2.1 h.2.1
  intro he
  rcases P.permitted_edge z m u he with
      hRole | hSplit | hTwo | hDevlin | hNormal
  · have h3 := hm.1
    rcases hRole.2.1 with h | h <;> omega
  · exact hNotOne hSplit.2.1
  · exact hNotLeaf hTwo.2.1
  · exact hNotLeaf hDevlin.2.1
  · exact hNotLeaf hNormal.2.1

/-- Moving a full ordered-pair type cut through an OLD 2-split
changes neither singleton coordinate; only the auxiliary bit
edge(m,a,b) is new. -/
theorem twoSplit_sameTwoType_succ_iff
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsTwoSplit H m) :
    H.SameTwoTypeBelow (m+1) a b c d ↔
      H.SameTwoTypeBelow m a b c d ∧
      (H.edge m a b ↔ H.edge m c d) := by
  constructor
  · intro h
    have hAux := h.2.2
    constructor
    · refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact h.1 hxy (by omega)
      · intro x y hxy hy
        exact h.2.1 hxy (by omega)
      · intro x hx
        exact hAux (a := x) (by omega)
    · exact hAux (a := m) (by omega)
  · rintro ⟨h,hBit⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      by_cases hyold : y < m
      · exact h.1 hxy hyold
      · have hym : y = m := by omega
        subst y
        exact iff_of_false
          (P.twoSplit_no_middle m x a hm)
          (P.twoSplit_no_middle m x c hm)
    · intro x y hxy hy
      by_cases hyold : y < m
      · exact h.2.1 hxy hyold
      · have hym : y = m := by omega
        subst y
        exact iff_of_false
          (P.twoSplit_no_middle m x b hm)
          (P.twoSplit_no_middle m x d hm)
    · intro x hx
      by_cases hxold : x < m
      · exact h.2.2 hxold
      · have hxm : x = m := by omega
        subst x
        exact hBit

/-- Every pair positively incident with a 2-split shares
the complete successor-cut pair type with any other positive
pair. This uses V2 and E, not S1/S2. -/
theorem twoSplit_positive_next_type
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsTwoSplit H m)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hAB : H.edge m a b) (hCD : H.edge m c d) :
    H.SameTwoTypeBelow (m+1) a b c d := by
  apply (P.twoSplit_sameTwoType_succ_iff m a b c d hm).mpr
  exact ⟨P.two_split_coherent m a b c d hm hab hcd
      ha hb hc hd hAB hCD, ⟨fun _ => hCD, fun _ => hAB⟩⟩

end RolePrediary
end DiaryLeafPriority
end ThreeUniformDiaries
