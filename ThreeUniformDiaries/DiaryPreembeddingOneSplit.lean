import ThreeUniformDiaries.DiaryMeetUnderCloseTypes
import ThreeUniformDiaries.DiaryLeafPriority
import ThreeUniformDiaries.DiaryEmbeddingExactOneMeets

/-!
# One-split placement and witness independence for diary pre-embeddings

The diary pre-embedding is defined on leaf vertices by a given
order-preserving induced map φ', and at each 1-split i by taking the
singleton type meet of the images of any two leaves witnessing i.

There are two independent tasks:
* placement: φ'(i-1) < meet(φ'u,φ'v) ≤ φ'(i);
* independence: the meet is unchanged when the witnessing leaves
  u,v are replaced by other witnesses of the same two singleton
  type classes.

The first part uses singleton type agreement through the predecessor
target cut and the actual first-disagreement edge at i, preserved
and reflected by an induced ordered map. The second part uses
singleton type agreement through φ'(i)+1 separately on the two
leaf classes, together with the just established upper meet bound.

This file proves both elementwise implications with explicit
hypotheses. They are intended as sublemmas in the pre-embedding
construction; checking that the native fused diary map supplies
all the needed close-type hypotheses is the next transfer step.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- The ordinary capped singleton type meet is symmetric. This
follows directly from symmetry of SameOneTypeBelow and min. -/
theorem oneMeetLevel_comm (H : Ordered3Graph Nat) (u v : Nat) :
    H.oneMeetLevel u v = H.oneMeetLevel v u := by
  have htype : (fun l => H.SameOneTypeBelow l u v) =
      (fun l => H.SameOneTypeBelow l v u) := by
    funext l
    apply propext
    constructor
    · intro h a b hab hbl
      exact (h a b hab hbl).symm
    · intro h a b hab hbl
      exact (h a b hab hbl).symm
  change Nat.findGreatest (fun l => H.SameOneTypeBelow l u v) (min u v) =
    Nat.findGreatest (fun l => H.SameOneTypeBelow l v u) (min v u)
  rw [htype, min_comm u v]

/-- Placement of the target singleton type split in its predecessor
interval. The source singleton meet is exactly the split vertex i;
the target singleton type agrees through image(i-1)+1, and the
source's first-disagreement edge bounds the target meet above by
image(i). No order assumption on the ORIGINAL unordered outer map
is needed once its refined composite is an induced ordered map. -/
theorem oneSplit_target_placement
    {H K : Ordered3Graph Nat}
    (φ : Embedding H K)
    (i u v : Nat)
    (hi : 0 < i) (hiu : i < u) (hiv : i < v)
    (hmeet : H.oneMeetLevel u v = i)
    (hSame : K.SameOneTypeBelow
      (φ (i-1) + 1) (φ u) (φ v)) :
    φ (i-1) < K.oneMeetLevel (φ u) (φ v) ∧
      K.oneMeetLevel (φ u) (φ v) ≤ φ i := by
  have hpred : i-1 < i := by omega
  have hpredU : φ (i-1) < φ u :=
    φ.strictMono (lt_trans hpred hiu)
  have hpredV : φ (i-1) < φ v :=
    φ.strictMono (lt_trans hpred hiv)
  have hcutU : φ (i-1) + 1 ≤ φ u := by omega
  have hcutV : φ (i-1) + 1 ≤ φ v := by omega
  have hLower :
      φ (i-1) + 1 ≤ K.oneMeetLevel (φ u) (φ v) :=
    (K.oneMeetLevel_ge_iff_sameOneTypeBelow
      (φ (i-1)+1) (φ u) (φ v)
      hcutU hcutV).mpr hSame
  obtain ⟨z, hzi, hdiff⟩ :=
    DiaryLeafPriority.oneMeetLevel_has_first_witness
      H u v i hmeet hiu hiv
  have hDiffImage :
      ¬ (K.edge (φ z) (φ i) (φ u) ↔
        K.edge (φ z) (φ i) (φ v)) := by
    intro h
    have hzu : H.edge z i u ↔
        K.edge (φ z) (φ i) (φ u) :=
      φ.edge_iff hzi hiu
    have hzv : H.edge z i v ↔
        K.edge (φ z) (φ i) (φ v) :=
      φ.edge_iff hzi hiv
    exact hdiff (hzu.trans (h.trans hzv.symm))
  have hUpper : K.oneMeetLevel (φ u) (φ v) ≤ φ i :=
    K.oneMeetLevel_le_of_edge_disagreement
      (φ u) (φ v) (φ z) (φ i)
      (φ.strictMono hzi) hDiffImage
  exact ⟨by omega, hUpper⟩

/-- Simultaneously replacing both witnesses of an early singleton
meet by vertices in their respective singleton type classes leaves
the target meet unchanged. This is exactly the independence
calculation used in the one-split case of diary pre-embedding. -/
theorem oneMeetLevel_pairWitness_independent
    (K : Ordered3Graph Nat)
    (M x y x' y' : Nat)
    (hMx : M < x) (hMy : M < y)
    (hMx' : M < x') (hMy' : M < y')
    (hSameX : K.SameOneTypeBelow (M+1) x x')
    (hSameY : K.SameOneTypeBelow (M+1) y y')
    (hEarly : K.oneMeetLevel x y ≤ M) :
    K.oneMeetLevel x' y' = K.oneMeetLevel x y := by
  have hFirst : K.oneMeetLevel x' y = K.oneMeetLevel x y :=
    K.oneMeetLevel_stable_under_close_one_types
      M x y x' hMx hMy hMx' hSameX hEarly
  have hEarly' : K.oneMeetLevel y x' ≤ M := by
    rw [K.oneMeetLevel_comm y x', hFirst]
    exact hEarly
  have hSecond : K.oneMeetLevel y' x' = K.oneMeetLevel y x' :=
    K.oneMeetLevel_stable_under_close_one_types
      M y x' y' hMy hMx' hMy' hSameY hEarly'
  calc
    K.oneMeetLevel x' y' = K.oneMeetLevel y' x' :=
      K.oneMeetLevel_comm x' y'
    _ = K.oneMeetLevel y x' := hSecond
    _ = K.oneMeetLevel x' y := K.oneMeetLevel_comm y x'
    _ = K.oneMeetLevel x y := hFirst

/-- An ordered induced target copy with the predecessor-cut I2
agreement and two corresponding next-cut singleton type agreements
gives a uniquely defined image of any source 1-split independent of
which two leaf witnesses are chosen. -/
theorem oneSplit_target_witness_independent
    {H K : Ordered3Graph Nat}
    (φ : Embedding H K)
    (i u v u' v' : Nat)
    (hi : 0 < i)
    (hiu : i < u) (hiv : i < v)
    (hiu' : i < u') (hiv' : i < v')
    (hmeet : H.oneMeetLevel u v = i)
    (hSamePred : K.SameOneTypeBelow
      (φ (i-1)+1) (φ u) (φ v))
    (hSameU : K.SameOneTypeBelow
      (φ i+1) (φ u) (φ u'))
    (hSameV : K.SameOneTypeBelow
      (φ i+1) (φ v) (φ v')) :
    K.oneMeetLevel (φ u') (φ v') =
      K.oneMeetLevel (φ u) (φ v) := by
  have hPlacement := φ.oneSplit_target_placement
    i u v hi hiu hiv hmeet hSamePred
  have hMx : φ i < φ u := φ.strictMono hiu
  have hMy : φ i < φ v := φ.strictMono hiv
  have hMx' : φ i < φ u' := φ.strictMono hiu'
  have hMy' : φ i < φ v' := φ.strictMono hiv'
  exact K.oneMeetLevel_pairWitness_independent
    (φ i) (φ u) (φ v) (φ u') (φ v')
    hMx hMy hMx' hMy' hSameU hSameV hPlacement.2

end Ordered3Graph
end ThreeUniformDiaries
