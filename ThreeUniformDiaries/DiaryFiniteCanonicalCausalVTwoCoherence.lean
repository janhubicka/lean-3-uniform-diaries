import ThreeUniformDiaries.DiaryFiniteCanonicalRankedRawVTwo
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalVOneCoherence
import ThreeUniformDiaries.DiaryCausalMarkerTypeTransport

/-!
# Genuine full V2 positive parent types in the final causal graph

Source-positive pairs at a shared canonical 2-split already have
identical full predecessor pair types in the ranked RAW union.
The literal causal marker completion only changes marker edges
on off-branch terminal pairs; neither compared original pair
is off-branch. Hence every auxiliary predecessor edge test is
UNCHANGED, including ones at off-path earlier vertices.

The two singleton coordinates use the actual ranked mask
coherence and the verified causal induction for literal
LexEarlier. This yields a genuine final SameTwoTypeBelow
at the actual numerical split cut, without an assumed global
prefix-uniform orientation.

This is source-positive cross-branch V2 compatibility; the
globally quantified target V2 coherence field, split witnesses,
permitted edge shapes, full finite diary and absorber are open.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- No auxiliary edge ending at an ordered pair on a single
source branch is changed by the causal marker extension. -/
theorem finiteCanonicalCausalMarkerGraph_aux_edge_iff_raw_on_branch
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (u v : Nat) (huv : u < v) (hvn : v < n)
    (x : Nat) :
    (finiteCanonicalCausalMarkerGraph DA).edge x
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val ↔
    (finiteCanonicalRankedRawGraph DA).edge x
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val := by
  let R := finiteCanonicalRankedRawGraph DA
  let M := finiteCanonicalRankedOffBranchMask DA
  let a := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i u (by omega))).val
  let b := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i v hvn)).val
  have hNo : ¬ M a b :=
    finiteCanonicalRankedOffBranchMask_same_branch_false
      DA i u v huv hvn
  have hFormula := causalMarkerLimit_formula R M
    (finiteCanonicalRankedOffBranchMask_later DA) x a b
  simpa only [finiteCanonicalCausalMarkerGraph,
    CausalMarkerColumn, hNo, false_and,
    and_false, or_false] using hFormula

/-- Source V2 positive parent compatibility across two genuine
canonical flip branches sharing a split, checked as a complete
full two-type at the final graph's ACTUAL rank cut. -/
theorem finiteCanonicalCausalMarkerGraph_sharedTwoSplit_positive_parent
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s u v w z : Nat)
    (hs : IsTwoSplit A s)
    (hsn : s < n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (huv : u < v) (hwz : w < z)
    (hvn : v < n) (hzn : z < n)
    (hsu : s < u) (hsw : s < w)
    (hu : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph i) u)
    (hv : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph i) v)
    (hw : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph j) w)
    (hz : IsLeaf ((finiteCanonicalSignRootedFamily DA).graph j) z)
    (hPosI : ((finiteCanonicalSignRootedFamily DA).graph i).edge s u v)
    (hPosJ : ((finiteCanonicalSignRootedFamily DA).graph j).edge s w z) :
    (finiteCanonicalCausalMarkerGraph DA).SameTwoTypeBelow
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j w (by omega))).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j z hzn)).val := by
  let F := finiteCanonicalSignRootedFamily DA
  let R := finiteCanonicalRankedRawGraph DA
  let M := finiteCanonicalRankedOffBranchMask DA
  let G := finiteCanonicalCausalMarkerGraph DA
  let m := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i s hsn)).val
  let a := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i u (by omega))).val
  let b := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA i v hvn)).val
  let c := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA j w (by omega))).val
  let d := (finiteCanonicalNodeIndex DA
    (finiteCanonicalNodeAt DA j z hzn)).val
  have huA : IsLeaf A u :=
    ((F.flip i).role_iff u hu.1 (by omega)).1.mpr hu
  have hvA : IsLeaf A v :=
    ((F.flip i).role_iff v hv.1 hvn).1.mpr hv
  have hwA : IsLeaf A w :=
    ((F.flip j).role_iff w hw.1 (by omega)).1.mpr hw
  have hzA : IsLeaf A z :=
    ((F.flip j).role_iff z hz.1 hzn).1.mpr hz
  have hRaw : R.SameTwoTypeBelow m a b c d :=
    finiteCanonicalRankedRaw_sharedTwoSplit_positive_parent
      DA i j s u v w z hs hsn hShared
      huv hwz hvn hzn hsu hsw hu hv hw hz hPosI hPosJ
  have hSharedRank :
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val =
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA j s hsn)).val := by
    have hEq : finiteCanonicalNodeAt DA i s hsn =
        finiteCanonicalNodeAt DA j s hsn :=
      Subtype.ext hShared
    exact congrArg
      (fun T : FiniteCanonicalSignRootedVertex DA =>
        (finiteCanonicalNodeIndex DA T).val) hEq
  have hma : m ≤ a :=
    (finiteCanonicalNodeAt_index_lt DA i s u hsu (by omega)).le
  have hmb : m ≤ b :=
    (finiteCanonicalNodeAt_index_lt DA i s v (by omega) hvn).le
  have hmc : m ≤ c := by
    have hj := finiteCanonicalNodeAt_index_lt DA j s w hsw (by omega)
    change (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA j s hsn)).val < c at hj
    dsimp only [m]
    rw [hSharedRank]
    exact hj.le
  have hmd : m ≤ d := by
    have hj := finiteCanonicalNodeAt_index_lt DA j s z (by omega) hzn
    change (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA j s hsn)).val < d at hj
    dsimp only [m]
    rw [hSharedRank]
    exact hj.le
  have hMaskAC : SameEarlierMarkerMask M m a c :=
    finiteCanonicalRankedOffBranchMask_sharedSplit_below
      DA i j s u w (Or.inr hs) hsn hShared
      hsu hsw (by omega) (by omega) huA hwA
  have hMaskBD : SameEarlierMarkerMask M m b d :=
    finiteCanonicalRankedOffBranchMask_sharedSplit_below
      DA i j s v z (Or.inr hs) hsn hShared
      (by omega) (by omega) hvn hzn hvA hzA
  have hLater : ∀ x y, M x y → x < y :=
    finiteCanonicalRankedOffBranchMask_later DA
  have hOneAC : G.SameOneTypeBelow m a c :=
    causalMarker_preserves_parent_oneType R G M m a c
      hma hmc hRaw.1 hMaskAC
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R M hLater x y a)
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R M hLater x y c)
  have hOneBD : G.SameOneTypeBelow m b d :=
    causalMarker_preserves_parent_oneType R G M m b d
      hmb hmd hRaw.2.1 hMaskBD
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R M hLater x y b)
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R M hLater x y d)
  have hAux : G.SameAuxTypeBelow m a b c d := by
    intro x hx
    have hI := finiteCanonicalCausalMarkerGraph_aux_edge_iff_raw_on_branch
      DA i u v huv hvn x
    have hJ := finiteCanonicalCausalMarkerGraph_aux_edge_iff_raw_on_branch
      DA j w z hwz hzn x
    exact hI.trans ((hRaw.2.2 hx).trans hJ.symm)
  exact ⟨hOneAC,hOneBD,hAux⟩

end DiaryLeafPriority
end ThreeUniformDiaries
