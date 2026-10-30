import ThreeUniformDiaries.DiaryPreembeddingSpec
import ThreeUniformDiaries.DiaryFiniteFlipTargetTransport

/-!
# Restrict a countable diary preembedding to any protected finite source copy

The published lower-bound argument uses a countable RoleDiary
preembedding into the target K. Its specification gives only
FORWARD marker roles on the source countable diary and exact
leaf-only numerical meets. To apply the verified finite flip
absorber, one needs a full FiniteLeafPreembedding, including
REFLECTION of all three roles and a finite target bound.

Marker-defined diary roles are mutually incompatible. Thus
forward role preservation and complete role coverage in the
countable source imply reflection, even though the target
preembedding is not a globally induced copy. Composing with
any finite exact-meet embedding into that source yields a
bounded finite leaf preembedding in the target. The bound can
be taken literally to be the image of the original finite
source cutoff, without assuming convexity or a finite target.

This does NOT upgrade mixed source pair meets of the countable
preembedding or infer inducedness of split-positive edges.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- All three marker roles of a genuine countable source diary
are reflected by any diary preembedding. Forward preservation
is enough because every source vertex has exactly one role,
and any two different roles disagree on a marker incidence. -/
theorem DiaryPreembeddingSpec.role_iff
    {H K : Ordered3Graph Nat} {θ : Nat → Nat}
    (DH : RoleDiary H) (P : DiaryPreembeddingSpec H K θ)
    (v : Nat) (hv3 : 3 ≤ v) :
    (IsLeaf K (θ v) ↔ IsLeaf H v) ∧
    (IsOneSplit K (θ v) ↔ IsOneSplit H v) ∧
    (IsTwoSplit K (θ v) ↔ IsTwoSplit H v) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hLeaf
      rcases DH.role_valid v hv3 with hl | ho | ht
      · exact hl
      · exact False.elim (hLeaf.2.1 (P.one_split_role v ho).2.1)
      · exact False.elim (hLeaf.2.2 (P.two_split_role v ht).2.2)
    · exact P.leaf_role v
  · constructor
    · intro hOne
      rcases DH.role_valid v hv3 with hl | ho | ht
      · exact False.elim ((P.leaf_role v hl).2.1 hOne.2.1)
      · exact ho
      · exact False.elim (hOne.2.2 (P.two_split_role v ht).2.2)
    · exact P.one_split_role v
  · constructor
    · intro hTwo
      rcases DH.role_valid v hv3 with hl | ho | ht
      · exact False.elim ((P.leaf_role v hl).2.2 hTwo.2.2)
      · exact False.elim ((P.one_split_role v ho).2.2 hTwo.2.2)
      · exact ht
    · exact P.two_split_role v

/-- Restrict the actually verified countable preembedding to
the image of an arbitrary finite diary under a genuine
FiniteMeetEmbedding into the source countable full diary.

The resulting bound is θ(e n), and every source vertex u<n
lands strictly below it. No extraneous mixed-meet condition
of the countable preembedding is postulated. -/
theorem DiaryPreembeddingSpec.comp_finiteMeetEmbedding
    {A H K : Ordered3Graph Nat}
    {n : Nat} {e θ : Nat → Nat}
    (DH : RoleDiary H)
    (P : DiaryPreembeddingSpec H K θ)
    (E : FiniteMeetEmbedding A H n e) :
    FiniteLeafPreembedding A K n (θ (e n))
      (fun u => θ (e u)) := by
  let f : Nat → Nat := fun u => θ (e u)
  refine {
    strictMono := ?_
    marker_zero := ?_
    marker_one := ?_
    marker_two := ?_
    image_bound := ?_
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro u v huv
    exact P.strictMono (E.strictMono huv)
  · change θ (e 0) = 0
    rw [E.marker_zero, P.marker_zero]
  · change θ (e 1) = 1
    rw [E.marker_one, P.marker_one]
  · change θ (e 2) = 2
    rw [E.marker_two, P.marker_two]
  · intro u hun
    exact P.strictMono (E.strictMono hun)
  · intro u hu3 hun
    have heu3 : 3 ≤ e u := E.nonmarker_image_ge_three u hu3
    have hRoles := P.role_iff DH (e u) heu3
    exact ⟨hRoles.1.trans (E.leaf_iff u hu3 hun),
      hRoles.2.1.trans (E.oneSplit_iff u hu3 hun),
      hRoles.2.2.trans (E.twoSplit_iff u hu3 hun)⟩
  · intro a b c hab hbc hcn ha hb hc
    have han : a < n := by omega
    have hbn : b < n := by omega
    have hHLeafA : IsLeaf H (e a) :=
      (E.leaf_iff a ha.1 han).mpr ha
    have hHLeafB : IsLeaf H (e b) :=
      (E.leaf_iff b hb.1 hbn).mpr hb
    have hHLeafC : IsLeaf H (e c) :=
      (E.leaf_iff c hc.1 hcn).mpr hc
    exact (P.leaf_edge_iff (e a) (e b) (e c)
      (E.strictMono hab) (E.strictMono hbc)
      hHLeafA hHLeafB hHLeafC).symm.trans
      (E.edge_iff a b c hab hbc hcn)
  · intro a b ha3 han hb3 hbn ha hb
    have hHLeafA : IsLeaf H (e a) :=
      (E.leaf_iff a ha3 han).mpr ha
    have hHLeafB : IsLeaf H (e b) :=
      (E.leaf_iff b hb3 hbn).mpr hb
    calc
      K.oneMeetLevel (θ (e a)) (θ (e b)) =
          θ (H.oneMeetLevel (e a) (e b)) :=
        P.leaf_one_meet (e a) (e b) hHLeafA hHLeafB
      _ = θ (e (A.oneMeetLevel a b)) :=
        congrArg θ (E.oneMeet a b ha3 han hb3 hbn)
  · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
      ha hb hc hd
    have hHLeafA : IsLeaf H (e a) :=
      (E.leaf_iff a ha3 han).mpr ha
    have hHLeafB : IsLeaf H (e b) :=
      (E.leaf_iff b hb3 hbn).mpr hb
    have hHLeafC : IsLeaf H (e c) :=
      (E.leaf_iff c hc3 hcn).mpr hc
    have hHLeafD : IsLeaf H (e d) :=
      (E.leaf_iff d hd3 hdn).mpr hd
    calc
      K.twoMeetLevel (θ (e a)) (θ (e b))
          (θ (e c)) (θ (e d)) =
          θ (H.twoMeetLevel (e a) (e b) (e c) (e d)) :=
        P.leaf_two_meet (e a) (e b) (e c) (e d)
          (E.strictMono hab) (E.strictMono hcd)
          hHLeafA hHLeafB hHLeafC hHLeafD
      _ = θ (e (A.twoMeetLevel a b c d)) :=
        congrArg θ (E.twoMeet a b c d hab hcd
          ha3 han hb3 hbn hc3 hcn hd3 hdn)

end DiaryLeafPriority
end ThreeUniformDiaries
