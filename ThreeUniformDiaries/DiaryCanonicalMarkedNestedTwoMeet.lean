import ThreeUniformDiaries.DiaryCanonicalMarkedNestedOneMeet
import ThreeUniformDiaries.DiaryFiniteLeafMeetS2Reduct

/-!
# Nested canonical supports: exact full S2 first disagreement

For four genuine selected leaves a<b and c<d, the full ordered-pair
S2 meet in the finite canonical support is the canonical rank of the
original ambient S2 meet. The strict source order, all S2 cap cases,
roles and marked rank bounds are kept explicitly.

This is a generator-specific theorem; it is not a global claim
that arbitrary finite compressions preserve every mixed type.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The FULL ordered-pair S2 meet of selected genuine leaves
is preserved exactly by increasing finite leaf-support
reindexing, including marker 1 and capped-leaf cases. -/
theorem finiteLeafMeetSupport_nested_rank_twoMeet
    {K : Ordered3Graph Nat}
    (D : RoleDiary K)
    (L : Finset Nat)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf K u)
    {a b c d : Nat}
    (hab : a < b) (hcd : c < d)
    (ha : a ∈ L) (hb : b ∈ L)
    (hc : c ∈ L) (hd : d ∈ L) :
    (finiteSupportGraph K (finiteLeafMeetSupport K L)).twoMeetLevel
        (finiteSupportRank (finiteLeafMeetSupport K L) a)
        (finiteSupportRank (finiteLeafMeetSupport K L) b)
        (finiteSupportRank (finiteLeafMeetSupport K L) c)
        (finiteSupportRank (finiteLeafMeetSupport K L) d) =
      finiteSupportRank (finiteLeafMeetSupport K L)
        (K.twoMeetLevel a b c d) := by
  classical
  let S : Finset Nat := finiteLeafMeetSupport K L
  let H : Ordered3Graph Nat := finiteSupportGraph K S
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker K L 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker K L 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker K L 2 (by omega)
  have hSelected (u : Nat) (hu : u ∈ L) :
      u ∈ S := mem_finiteLeafMeetSupport_leaf K L u hu
  have hRole (u : Nat) (hu : u ∈ L) :
      IsLeaf H (finiteSupportRank S u) := by
    have huS := hSelected u hu
    have hr := finiteSupportRank_spec S u huS
    have hu3 : 3 ≤ u := (hLeaves u hu).1
    have hImage : 3 ≤ finiteSupportIndex S
        (finiteSupportRank S u) := by
      rw [hr.2]
      exact hu3
    have hr3 : 3 ≤ finiteSupportRank S u :=
      finiteSupportIndex_ge_three_of_image S
        (finiteSupportRank S u) h0 h1 h2 hr.1 hImage
    have hIff :=
      finiteSupportGraph_leaf_iff (G := K) (S := S)
        h0 h1 h2 (finiteSupportRank S u) hr3 hr.1
    apply hIff.mpr
    rw [hr.2]
    exact hLeaves u hu
  have haS := hSelected a ha
  have hbS := hSelected b hb
  have hcS := hSelected c hc
  have hdS := hSelected d hd
  have ra := finiteSupportRank_spec S a haS
  have rb := finiteSupportRank_spec S b hbS
  have rc := finiteSupportRank_spec S c hcS
  have rd := finiteSupportRank_spec S d hdS
  have hrAB : finiteSupportRank S a < finiteSupportRank S b :=
    finiteSupportRank_lt S haS hbS hab
  have hrCD : finiteSupportRank S c < finiteSupportRank S d :=
    finiteSupportRank_lt S hcS hdS hcd
  have hMeet :
      K.twoMeetLevel
          (finiteSupportIndex S (finiteSupportRank S a))
          (finiteSupportIndex S (finiteSupportRank S b))
          (finiteSupportIndex S (finiteSupportRank S c))
          (finiteSupportIndex S (finiteSupportRank S d)) =
        finiteSupportIndex S
          (H.twoMeetLevel (finiteSupportRank S a)
            (finiteSupportRank S b) (finiteSupportRank S c)
            (finiteSupportRank S d)) :=
    (finiteLeafMeetSupport_reindexed_S2_exact_and_role
      D hLeaves
      (finiteSupportRank S a) (finiteSupportRank S b)
      (finiteSupportRank S c) (finiteSupportRank S d)
      ra.1 rb.1 rc.1 rd.1 hrAB hrCD
      (hRole a ha) (hRole b hb) (hRole c hc) (hRole d hd)).1
  rw [ra.2, rb.2, rc.2, rd.2] at hMeet
  have hBound :
      H.twoMeetLevel (finiteSupportRank S a)
        (finiteSupportRank S b) (finiteSupportRank S c)
        (finiteSupportRank S d) < S.card := by
    have hLe := H.twoMeetLevel_le_min
      (finiteSupportRank S a) (finiteSupportRank S b)
      (finiteSupportRank S c) (finiteSupportRank S d)
    exact lt_of_le_of_lt (hLe.trans (min_le_left _ _)) ra.1
  change H.twoMeetLevel (finiteSupportRank S a)
      (finiteSupportRank S b) (finiteSupportRank S c)
      (finiteSupportRank S d) =
      finiteSupportRank S (K.twoMeetLevel a b c d)
  calc
    H.twoMeetLevel (finiteSupportRank S a)
        (finiteSupportRank S b) (finiteSupportRank S c)
        (finiteSupportRank S d) =
        finiteSupportRank S
          (finiteSupportIndex S
            (H.twoMeetLevel (finiteSupportRank S a)
              (finiteSupportRank S b) (finiteSupportRank S c)
              (finiteSupportRank S d))) :=
      (finiteSupportRank_of_index S _ hBound).symm
    _ = finiteSupportRank S (K.twoMeetLevel a b c d) :=
      congrArg (finiteSupportRank S) hMeet.symm

end DiaryLeafPriority
end ThreeUniformDiaries
