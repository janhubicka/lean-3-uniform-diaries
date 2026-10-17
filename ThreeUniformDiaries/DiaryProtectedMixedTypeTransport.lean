import ThreeUniformDiaries.DiaryProtectedMixedEdgeShapes
import ThreeUniformDiaries.DiaryOnePassGlobalOneTypeTransport

/-!
# Exact type reductions and one-pass transport for mixed split pairs

A protected ordered pair need not consist of leaves. The existing global
one-pass full two-type theorem is restricted to pairs of source leaves,
so applying it to a pair containing a split is invalid.

The E1--E5 edge shapes make the mixed case more elementary:
* auxiliary tests at every positive coordinate vanish as soon as one
  endpoint is a genuine one-/two-split;
* singleton tests ending at a genuine split have no middle coordinate
  at or above 3.

Thus mixed auxiliary types depend only on marker zero, while the
singleton type of a split is determined by the three marker levels.
Old marker edges are copied exactly by the induced old-vertex map.
We obtain exact original-cut transport for pairs whose corresponding
coordinates are either both leaves or both splits.

No source S1/S2, universal old-cut preservation, finite-diary interface,
or every-flip absorption is assumed or concluded.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- For two pairs each containing a genuine split, all positive
auxiliary tests are false. The entire auxiliary type at a positive
cut is exactly the bit at the zero marker. -/
theorem RolePrediary.mixed_auxType_iff_zero
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : 0 < m)
    (hAB : IsDiarySplit H a ∨ IsDiarySplit H b)
    (hCD : IsDiarySplit H c ∨ IsDiarySplit H d) :
    H.SameAuxTypeBelow m a b c d ↔
      (H.edge 0 a b ↔ H.edge 0 c d) := by
  constructor
  · intro h
    exact h hm
  · intro hzero x hx
    by_cases hxZero : x = 0
    · subst x
      exact hzero
    · have hxPos : 0 < x := by omega
      exact P.mixed_pairs_positive_aux_agree
        a b c d m hAB hCD x hxPos hx

/-- A split endpoint can only receive the E1 marker-column tests.
Consequently equality of the singleton types of two splits is
constant beyond cut three. -/
theorem RolePrediary.split_oneType_stable_after_three
    (P : RolePrediary H) (m u v : Nat)
    (hm : 3 ≤ m)
    (hu : IsDiarySplit H u)
    (hv : IsDiarySplit H v) :
    H.SameOneTypeBelow m u v ↔
      H.SameOneTypeBelow 3 u v := by
  constructor
  · intro h a b hab hb
    exact h hab (by omega)
  · intro h a b hab hb
    by_cases hb3 : b < 3
    · exact h hab hb3
    · have hbLate : 3 ≤ b := by omega
      exact iff_of_false
        (P.split_no_late_singleton_test a b u hu hbLate)
        (P.split_no_late_singleton_test a b v hv hbLate)

/-- The induced copy reflects split roles as predicates actually
defined by source and target marker edges. -/
theorem onePassOldImage_isDiarySplit
    (H : Ordered3Graph Nat) (z : Nat) :
    IsDiarySplit H z ↔
      IsDiarySplit (onePassRawTarget H) (onePassOldImage H z) := by
  unfold IsDiarySplit
  exact or_congr
    (onePassRawTarget_old_oneSplit_iff H z)
    (onePassRawTarget_old_twoSplit_iff H z)

/-- Every original event-block start remains at or above cut three
once its original cut does. -/
theorem onePassBefore_ge_three
    (H : Ordered3Graph Nat) (m : Nat) (hm : 3 ≤ m) :
    3 ≤ onePassBefore H m := by
  unfold onePassBefore
  omega

/-- The singleton type of any two split vertices is transported
between arbitrary cuts >= 3. All actual old-marker bits are copied,
and no new test can end at a split vertex. -/
theorem onePass_split_oneType_transport
    (P : RolePrediary H) (m n u v : Nat)
    (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hu : IsDiarySplit H u) (hv : IsDiarySplit H v) :
    H.SameOneTypeBelow m u v ↔
      (onePassRawTarget H).SameOneTypeBelow n
        (onePassOldImage H u) (onePassOldImage H v) := by
  have huTarget :
      IsDiarySplit (onePassRawTarget H) (onePassOldImage H u) :=
    (onePassOldImage_isDiarySplit H u).mp hu
  have hvTarget :
      IsDiarySplit (onePassRawTarget H) (onePassOldImage H v) :=
    (onePassOldImage_isDiarySplit H v).mp hv
  calc
    H.SameOneTypeBelow m u v ↔ H.SameOneTypeBelow 3 u v :=
      P.split_oneType_stable_after_three m u v hm hu hv
    _ ↔ (onePassRawTarget H).SameOneTypeBelow 3
            (onePassOldImage H u) (onePassOldImage H v) :=
      onePass_oneTypeBelow_three_iff H u v
    _ ↔ (onePassRawTarget H).SameOneTypeBelow n
            (onePassOldImage H u) (onePassOldImage H v) :=
      ((onePassRawTarget_isPrediary P).split_oneType_stable_after_three
        n (onePassOldImage H u) (onePassOldImage H v)
        hn huTarget hvTarget).symm

/-- Auxiliary type transport for ANY two split-containing pairs.
Both original and target cuts can be arbitrary positive integers:
the only nontrivial bit is copied marker zero. -/
theorem onePass_mixed_auxType_transport
    (P : RolePrediary H) (m n a b c d : Nat)
    (hm : 0 < m) (hn : 0 < n)
    (hAB : IsDiarySplit H a ∨ IsDiarySplit H b)
    (hCD : IsDiarySplit H c ∨ IsDiarySplit H d) :
    H.SameAuxTypeBelow m a b c d ↔
      (onePassRawTarget H).SameAuxTypeBelow n
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) := by
  let G := onePassRawTarget H
  have hABTarget :
      IsDiarySplit G (onePassOldImage H a) ∨
        IsDiarySplit G (onePassOldImage H b) := by
    rcases hAB with ha | hb
    · exact Or.inl ((onePassOldImage_isDiarySplit H a).mp ha)
    · exact Or.inr ((onePassOldImage_isDiarySplit H b).mp hb)
  have hCDTarget :
      IsDiarySplit G (onePassOldImage H c) ∨
        IsDiarySplit G (onePassOldImage H d) := by
    rcases hCD with hc | hd
    · exact Or.inl ((onePassOldImage_isDiarySplit H c).mp hc)
    · exact Or.inr ((onePassOldImage_isDiarySplit H d).mp hd)
  have hABZero :
      G.edge 0 (onePassOldImage H a) (onePassOldImage H b) ↔
      H.edge 0 a b := by
    simpa only [onePassOldImage_zero] using
      (onePassRawTarget_edge_image_iff H 0 a b)
  have hCDZero :
      G.edge 0 (onePassOldImage H c) (onePassOldImage H d) ↔
      H.edge 0 c d := by
    simpa only [onePassOldImage_zero] using
      (onePassRawTarget_edge_image_iff H 0 c d)
  have hZero :
      (H.edge 0 a b ↔ H.edge 0 c d) ↔
      (G.edge 0 (onePassOldImage H a) (onePassOldImage H b) ↔
        G.edge 0 (onePassOldImage H c) (onePassOldImage H d)) := by
    constructor
    · intro h
      exact hABZero.trans (h.trans hCDZero.symm)
    · intro h
      exact hABZero.symm.trans (h.trans hCDZero)
  calc
    H.SameAuxTypeBelow m a b c d ↔
        (H.edge 0 a b ↔ H.edge 0 c d) :=
      P.mixed_auxType_iff_zero m a b c d hm hAB hCD
    _ ↔ (G.edge 0 (onePassOldImage H a) (onePassOldImage H b) ↔
        G.edge 0 (onePassOldImage H c) (onePassOldImage H d)) := hZero
    _ ↔ G.SameAuxTypeBelow n
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) :=
      ((onePassRawTarget_isPrediary P).mixed_auxType_iff_zero
        n (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)
        hn hABTarget hCDTarget).symm

/-- At original cut m, an aligned pair of LEAF coordinates has the
existing global leaf transport; an aligned pair of SPLIT coordinates
has the marker-only transport above. We do not claim a cross-role
leaf/split transport. -/
theorem onePass_aligned_oneType_transport
    (P : RolePrediary H) (m u v : Nat)
    (hm : 3 ≤ m)
    (hAligned :
      (IsLeaf H u ∧ IsLeaf H v ∧ m ≤ u ∧ m ≤ v) ∨
      (IsDiarySplit H u ∧ IsDiarySplit H v)) :
    H.SameOneTypeBelow m u v ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H m)
        (onePassOldImage H u) (onePassOldImage H v) := by
  rcases hAligned with ⟨hu, hv, hmu, hmv⟩ | ⟨hu, hv⟩
  · exact onePass_global_oneType_transport P m u v hm hu hv hmu hmv
  · exact onePass_split_oneType_transport P m (onePassBefore H m)
      u v hm (onePassBefore_ge_three H m hm) hu hv

/-- Exact FULL two-type transport for protected mixed pairs when
corresponding coordinates have aligned roles (leaf/leaf or
split/split). In contrast to the leaf-only transport theorem,
at least one member of each PAIR is a split. This covers the
role-aligned mixed comparison needed by protected copies; cross-role
comparisons and the finite-diary embedding remain separate. -/
theorem onePass_mixed_twoType_transport
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : 3 ≤ m)
    (hAC :
      (IsLeaf H a ∧ IsLeaf H c ∧ m ≤ a ∧ m ≤ c) ∨
      (IsDiarySplit H a ∧ IsDiarySplit H c))
    (hBD :
      (IsLeaf H b ∧ IsLeaf H d ∧ m ≤ b ∧ m ≤ d) ∨
      (IsDiarySplit H b ∧ IsDiarySplit H d))
    (hAB : IsDiarySplit H a ∨ IsDiarySplit H b)
    (hCD : IsDiarySplit H c ∨ IsDiarySplit H d) :
    H.SameTwoTypeBelow m a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassBefore H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) := by
  have hFirst :=
    onePass_aligned_oneType_transport P m a c hm hAC
  have hSecond :=
    onePass_aligned_oneType_transport P m b d hm hBD
  have hAux :=
    onePass_mixed_auxType_transport P m (onePassBefore H m)
      a b c d (by omega)
      (by have h := onePassBefore_ge_three H m hm; omega)
      hAB hCD
  exact and_congr hFirst (and_congr hSecond hAux)

end DiaryLeafPriority
end ThreeUniformDiaries
