import ThreeUniformDiaries.DiaryFiniteCanonicalRankedRawVTwo
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalVTwoCoherence

/-!
# Full original source pair-type agreement survives literal causal completion

The full V2-positive parent lemma does not directly apply to the
two pairs witnessing an S2 split: one is positive at that split
and the other is negative. What we need instead is preservation
of arbitrary source full pair-type agreement THROUGH the old
split, without a positivity condition.

The old raw sign-rooted type preservation theorem transports all
three predecessor components from a source flip into the raw
amalgam. The rank-cut lemmas then retain this equality at the
ACTUAL numerical cut, even with inserted off-path vertices and
same-level ties.

The literal causal marker extension preserves each singleton
component by the prefix-geometric mask agreement and the
previously validated causal type induction. Auxiliary tests do
not change because both compared ordered pairs lie on the same
original source branch.

This is precisely the lower-bound half of the exact S2 witness
meet proof. No diary witness or full S2 result is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Arbitrary SOURCE full pair-type agreement through a genuine
source 2-split is inherited by the ACTUAL ranked raw union.
The two ordered source pairs need not have the same E3 incidence
at this split; they need only agree below the split. -/
theorem finiteCanonicalRankedRaw_original_twoType_at_twoSplit
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (s a b c d : Nat)
    (hsn : s < n) (hsa : s < a) (hsc : s < c)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (hSource :
      ((finiteCanonicalSignRootedFamily DA).graph i).SameTwoTypeBelow
        s a b c d) :
    (finiteCanonicalRankedRawGraph DA).SameTwoTypeBelow
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i a (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i b hbn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i c (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i d hdn)).val := by
  let F := finiteCanonicalSignRootedFamily DA
  have hRaw : F.RawSameTwoTypeBelow s
      (F.node i a) (F.node i b)
      (F.node i c) (F.node i d) :=
    (F.rawSameTwoTypeBelow_iff_source i s a b c d
      hsa.le hsc.le hab hcd hbn hdn).mpr hSource
  have hOneAC : F.RawCrossOneTypeBelow s
      (F.node i a) (F.node i c) := hRaw.1
  have hOneBD : F.RawCrossOneTypeBelow s
      (F.node i b) (F.node i d) := hRaw.2.1
  have hAux : F.RawCrossAuxTypeBelow s
      (F.node i a) (F.node i b)
      (F.node i c) (F.node i d) := hRaw.2.2
  refine ⟨
    finiteCanonicalRankedRaw_crossOneType_at_shared_cut
      DA i i s a c hsn rfl hsa.le hsc.le
      (by omega) (by omega) hOneAC,
    finiteCanonicalRankedRaw_crossOneType_at_shared_cut
      DA i i s b d hsn rfl (by omega) (by omega)
      hbn hdn hOneBD,
    finiteCanonicalRankedRaw_crossAux_at_shared_cut
      DA i i s a b c d hsn rfl hsa.le hsc.le
      hab hcd hbn hdn hAux⟩

/-- Arbitrary full two-type equality of two ordered leaf pairs
below a source 2-split remains valid in the FINAL causal graph
at that split's exact numerical rank. This allows pairs
on OPPOSITE E3 sides of the split. -/
theorem finiteCanonicalCausalMarkerGraph_original_twoType_at_twoSplit
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (s a b c d : Nat)
    (hs : IsTwoSplit A s)
    (hsn : s < n) (hsa : s < a) (hsc : s < c)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hc : IsLeaf A c) (hd : IsLeaf A d)
    (hSource :
      ((finiteCanonicalSignRootedFamily DA).graph i).SameTwoTypeBelow
        s a b c d) :
    (finiteCanonicalCausalMarkerGraph DA).SameTwoTypeBelow
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i a (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i b hbn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i c (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i d hdn)).val := by
  let R := finiteCanonicalRankedRawGraph DA
  let M := finiteCanonicalRankedOffBranchMask DA
  let G := finiteCanonicalCausalMarkerGraph DA
  let m := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i s hsn)).val
  let aa := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i a (by omega))).val
  let bb := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i b hbn)).val
  let cc := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i c (by omega))).val
  let dd := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i d hdn)).val
  have hRaw : R.SameTwoTypeBelow m aa bb cc dd :=
    finiteCanonicalRankedRaw_original_twoType_at_twoSplit
      DA i s a b c d hsn hsa hsc hab hcd hbn hdn hSource
  have hMA : m ≤ aa :=
    (finiteCanonicalNodeAt_index_lt DA i s a hsa (by omega)).le
  have hMB : m ≤ bb :=
    (finiteCanonicalNodeAt_index_lt DA i s b (by omega) hbn).le
  have hMC : m ≤ cc :=
    (finiteCanonicalNodeAt_index_lt DA i s c hsc (by omega)).le
  have hMD : m ≤ dd :=
    (finiteCanonicalNodeAt_index_lt DA i s d (by omega) hdn).le
  have hMaskAC : SameEarlierMarkerMask M m aa cc :=
    finiteCanonicalRankedOffBranchMask_sharedSplit_below
      DA i i s a c (Or.inr hs) hsn rfl
      hsa hsc (by omega) (by omega) ha hc
  have hMaskBD : SameEarlierMarkerMask M m bb dd :=
    finiteCanonicalRankedOffBranchMask_sharedSplit_below
      DA i i s b d (Or.inr hs) hsn rfl
      (by omega) (by omega) hbn hdn hb hd
  have hLater : ∀ y z : Nat, M y z → y < z :=
    finiteCanonicalRankedOffBranchMask_later DA
  have hOneAC : G.SameOneTypeBelow m aa cc :=
    causalMarker_preserves_parent_oneType R G M m aa cc
      hMA hMC hRaw.1 hMaskAC
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R M hLater x y aa)
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R M hLater x y cc)
  have hOneBD : G.SameOneTypeBelow m bb dd :=
    causalMarker_preserves_parent_oneType R G M m bb dd
      hMB hMD hRaw.2.1 hMaskBD
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R M hLater x y bb)
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R M hLater x y dd)
  have hAux : G.SameAuxTypeBelow m aa bb cc dd := by
    intro x hx
    have hI := finiteCanonicalCausalMarkerGraph_aux_edge_iff_raw_on_branch
      DA i a b hab hbn x
    have hJ := finiteCanonicalCausalMarkerGraph_aux_edge_iff_raw_on_branch
      DA i c d hcd hdn x
    exact hI.trans ((hRaw.2.2 hx).trans hJ.symm)
  exact ⟨hOneAC,hOneBD,hAux⟩

end DiaryLeafPriority
end ThreeUniformDiaries
