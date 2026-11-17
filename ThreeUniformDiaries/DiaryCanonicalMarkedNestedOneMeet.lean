import ThreeUniformDiaries.DiaryCanonicalMarkedRawRestriction
import ThreeUniformDiaries.DiaryFiniteLeafMeetV1Witness
import ThreeUniformDiaries.DiaryFiniteLeafMeetS1Reduct

/-!
# Nested canonical supports: exact S1 first disagreement

Let L be genuine leaves of a countable full RoleDiary K and
S=S_K(L) their exact finite S1/full-S2 generated support.
The increasing rank map r_S is NOT globally type-respecting on K;
finite compression can delete nonselected tests.

Nevertheless, the checked selected-leaf S1 compression theorem
proves exactly the equation needed for every chosen pair of
distinct selected leaves a,b in L:

   oneMeet_{K_L}(r_S(a),r_S(b)) = r_S(oneMeet_K(a,b))

This is the first generator-specific ingredient of nested
marked-subdiary support naturality, not the complete theorem.
No false global meet preservation is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The *true* singleton-meet of ANY two distinct selected old
leaves is taken by the canonical finite support rank map to
the singleton-meet in the induced finite support. No monotonicity
of the arbitrary original marked labels is assumed. -/
theorem finiteLeafMeetSupport_nested_rank_oneMeet
    {K : Ordered3Graph Nat}
    (D : RoleDiary K)
    (L : Finset Nat)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf K u)
    {a b : Nat} (ha : a ∈ L) (hb : b ∈ L)
    (hne : a ≠ b) :
    (finiteSupportGraph K (finiteLeafMeetSupport K L)).oneMeetLevel
        (finiteSupportRank (finiteLeafMeetSupport K L) a)
        (finiteSupportRank (finiteLeafMeetSupport K L) b) =
      finiteSupportRank (finiteLeafMeetSupport K L)
        (K.oneMeetLevel a b) := by
  classical
  let S : Finset Nat := finiteLeafMeetSupport K L
  let H : Ordered3Graph Nat := finiteSupportGraph K S
  have hOrdered (u v : Nat) (hu : u ∈ L) (hv : v ∈ L)
      (huv : u < v) :
      H.oneMeetLevel (finiteSupportRank S u) (finiteSupportRank S v) =
        finiteSupportRank S (K.oneMeetLevel u v) := by
    have huS : u ∈ S := mem_finiteLeafMeetSupport_leaf K L u hu
    have hvS : v ∈ S := mem_finiteLeafMeetSupport_leaf K L v hv
    have huRank := finiteSupportRank_spec S u huS
    have hvRank := finiteSupportRank_spec S v hvS
    have huvRank : finiteSupportRank S u < finiteSupportRank S v :=
      finiteSupportRank_lt S huS hvS huv
    have huSelected : finiteSupportIndex S (finiteSupportRank S u) ∈ L := by
      rw [huRank.2]
      exact hu
    have hvSelected : finiteSupportIndex S (finiteSupportRank S v) ∈ L := by
      rw [hvRank.2]
      exact hv
    have hMeet :
        K.oneMeetLevel
            (finiteSupportIndex S (finiteSupportRank S u))
            (finiteSupportIndex S (finiteSupportRank S v)) =
          finiteSupportIndex S
            (H.oneMeetLevel (finiteSupportRank S u)
              (finiteSupportRank S v)) :=
      (finiteLeafMeetSupport_selected_S1_exact_and_role
        D hLeaves
        (finiteSupportRank S u) (finiteSupportRank S v)
        huRank.1 hvRank.1 huvRank huSelected hvSelected).1
    rw [huRank.2, hvRank.2] at hMeet
    have hBound :
        H.oneMeetLevel (finiteSupportRank S u)
            (finiteSupportRank S v) < S.card := by
      have hLe := H.oneMeetLevel_le_min
        (finiteSupportRank S u) (finiteSupportRank S v)
      omega
    calc
      H.oneMeetLevel (finiteSupportRank S u)
          (finiteSupportRank S v) =
          finiteSupportRank S
            (finiteSupportIndex S
              (H.oneMeetLevel (finiteSupportRank S u)
                (finiteSupportRank S v))) :=
          (finiteSupportRank_of_index S _ hBound).symm
      _ = finiteSupportRank S (K.oneMeetLevel u v) :=
        congrArg (finiteSupportRank S) hMeet.symm
  change H.oneMeetLevel (finiteSupportRank S a)
      (finiteSupportRank S b) =
      finiteSupportRank S (K.oneMeetLevel a b)
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact hOrdered a b ha hb hab
  · calc
      H.oneMeetLevel (finiteSupportRank S a)
          (finiteSupportRank S b) =
          H.oneMeetLevel (finiteSupportRank S b)
            (finiteSupportRank S a) :=
        finiteLeafMeet_oneMeet_comm H _ _
      _ = finiteSupportRank S (K.oneMeetLevel b a) :=
        hOrdered b a hb ha hba
      _ = finiteSupportRank S (K.oneMeetLevel a b) :=
        congrArg (finiteSupportRank S)
          (finiteLeafMeet_oneMeet_comm K a b).symm

end DiaryLeafPriority
end ThreeUniformDiaries
