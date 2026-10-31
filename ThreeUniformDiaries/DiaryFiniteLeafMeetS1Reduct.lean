import ThreeUniformDiaries.DiaryFiniteLeafMeetOnlySelectedLeaves
import ThreeUniformDiaries.DiaryFiniteLeafMeetFirstDisagreement

/-!
# The S1 axiom of the finite leaf-meet reduct

All genuine leaves of the generated support S_L come from the
selected finite leaf set L. For distinct selected leaves, S1 in
the ambient countable diary supplies a genuine source one-split m.
The generator m belongs to S_L, and the increasing support
enumeration has a unique index k for it. Since m is a split
strictly below both leaves, k is a genuine nonmarker index before
the indices of both leaves.

The already checked first-disagreement theorem says the indexed
singleton meet is EXACTLY k, and marker role reflection makes k
a genuine one-split of the finite induced structure.

Thus the S1 splitting axiom holds for every pair of distinct
finite target leaves, not just a preselected pair.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {L : Finset Nat}

/-- An increasing finite enumeration is monotone on indices
inside its actual cardinality. -/
theorem finiteSupportIndex_mono_below
    (S : Finset Nat) (i j : Nat)
    (hi : i < S.card) (hj : j < S.card)
    (hij : i ≤ j) :
    finiteSupportIndex S i ≤ finiteSupportIndex S j := by
  rcases lt_or_eq_of_le hij with hlt | heq
  · exact (finiteSupportIndex_strictMono S i j hlt hj).le
  · subst j
    exact le_refl _

/-- The first three selected indices are precisely the old
markers. Hence a selected old vertex with true level >=3
necessarily has a new index >=3. -/
theorem finiteSupportIndex_ge_three_of_image
    (S : Finset Nat) (i : Nat)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (hi : i < S.card)
    (hImage : 3 ≤ finiteSupportIndex S i) :
    3 ≤ i := by
  obtain ⟨_hCard,hZero,hOne,hTwo⟩ :=
    finiteSupportIndex_initial_markers S h0 h1 h2
  by_contra hlt
  have hiSmall : i < 3 := by omega
  have hiVal : finiteSupportIndex S i = i := by
    interval_cases i
    · exact hZero
    · exact hOne
    · exact hTwo
  rw [hiVal] at hImage
  omega

/-- An original selected one-split below a selected vertex is
also strictly earlier in the enumeration than that vertex. -/
theorem finiteSupportIndex_lt_of_image_lt
    (S : Finset Nat)
    (k i : Nat) (hk : k < S.card) (hi : i < S.card)
    (hOld : finiteSupportIndex S k < finiteSupportIndex S i) :
    k < i := by
  by_contra hn
  have hik : i ≤ k := by omega
  have hBackward : finiteSupportIndex S i ≤ finiteSupportIndex S k :=
    finiteSupportIndex_mono_below S i k hi hk hik
  omega

/-- Every ordered pair of selected old leaves has a proper
one-split as its exact new singleton meet. This is stated
using membership in L so that source witnesses are genuinely
present in the generated finite support. -/
theorem finiteLeafMeetSupport_selected_S1_exact_and_role
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (i j : Nat)
    (hi : i < (finiteLeafMeetSupport G L).card)
    (hj : j < (finiteLeafMeetSupport G L).card)
    (hij : i < j)
    (hUi : finiteSupportIndex (finiteLeafMeetSupport G L) i ∈ L)
    (hVj : finiteSupportIndex (finiteLeafMeetSupport G L) j ∈ L) :
    G.oneMeetLevel
        (finiteSupportIndex (finiteLeafMeetSupport G L) i)
        (finiteSupportIndex (finiteLeafMeetSupport G L) j) =
      finiteSupportIndex (finiteLeafMeetSupport G L)
        ((finiteSupportGraph G (finiteLeafMeetSupport G L)).oneMeetLevel i j) ∧
    IsOneSplit (finiteSupportGraph G (finiteLeafMeetSupport G L))
      ((finiteSupportGraph G (finiteLeafMeetSupport G L)).oneMeetLevel i j) := by
  classical
  let S := finiteLeafMeetSupport G L
  let H := finiteSupportGraph G S
  let u := finiteSupportIndex S i
  let v := finiteSupportIndex S j
  let m := G.oneMeetLevel u v
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker G L 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker G L 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker G L 2 (by omega)
  have huLeaf : IsLeaf G u := hLeaves u hUi
  have hvLeaf : IsLeaf G v := hLeaves v hVj
  have huv : u < v := finiteSupportIndex_strictMono S i j hij hj
  have hSourceSplit : IsOneSplit G m :=
    D.singleton_meets u v huLeaf hvLeaf (ne_of_lt huv)
  have hmMem : m ∈ S :=
    mem_finiteLeafMeetSupport_oneMeet G L u v hUi hVj (ne_of_lt huv)
  obtain ⟨k,hk,hkm⟩ := finiteSupportIndex_surjective_on S m hmMem
  have hk3 : 3 ≤ k :=
    finiteSupportIndex_ge_three_of_image S k h0 h1 h2 hk
      (by simpa only [hkm] using hSourceSplit.1)
  have hmBound : m ≤ min u v := G.oneMeetLevel_le_min u v
  have hmu : m < u := by
    have hle : m ≤ u := hmBound.trans (min_le_left _ _)
    have hne : m ≠ u := by
      intro h
      have hOne : IsOneSplit G u := by
        simpa only [h] using hSourceSplit
      exact huLeaf.2.1 hOne.2.1
    omega
  have hmv : m < v := by
    have hle : m ≤ v := hmBound.trans (min_le_right _ _)
    have hne : m ≠ v := by
      intro h
      have hOne : IsOneSplit G v := by
        simpa only [h] using hSourceSplit
      exact hvLeaf.2.1 hOne.2.1
    omega
  have hki : k < i := finiteSupportIndex_lt_of_image_lt
    S k i hk hi (by simpa only [hkm] using hmu)
  have hkj : k < j := finiteSupportIndex_lt_of_image_lt
    S k j hk hj (by simpa only [hkm] using hmv)
  have hTargetSplit : IsOneSplit H k :=
    (finiteSupportGraph_oneSplit_iff
      (G := G) (S := S) h0 h1 h2 k hk3 hk).mpr
      (by simpa only [hkm] using hSourceSplit)
  have hExact : H.oneMeetLevel i j = k :=
    finiteSupportGraph_oneMeet_exact_at_retained_oneSplit
      D h0 h1 h2 i j k u v m hi hj hk
      hij hk3 hki hkj rfl rfl hkm hSourceSplit rfl
  rw [hExact]
  exact ⟨hkm.symm,hTargetSplit⟩

/-- The original S1 role conclusion follows from the stronger
EXACT numerical singleton-meet transport, with no duplicate
first-disagreement proof. -/
theorem finiteLeafMeetSupport_selected_S1
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (i j : Nat)
    (hi : i < (finiteLeafMeetSupport G L).card)
    (hj : j < (finiteLeafMeetSupport G L).card)
    (hij : i < j)
    (hUi : finiteSupportIndex (finiteLeafMeetSupport G L) i ∈ L)
    (hVj : finiteSupportIndex (finiteLeafMeetSupport G L) j ∈ L) :
    IsOneSplit (finiteSupportGraph G (finiteLeafMeetSupport G L))
      ((finiteSupportGraph G (finiteLeafMeetSupport G L)).oneMeetLevel i j) :=
  (finiteLeafMeetSupport_selected_S1_exact_and_role
    D hLeaves i j hi hj hij hUi hVj).2

/-- Genuine finite target leaves are exactly old selected leaves,
so the preceding proof gives the complete bounded S1 axiom on
the reindexed support. -/
theorem finiteLeafMeetSupport_reindexed_S1
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (i j : Nat)
    (hi : i < (finiteLeafMeetSupport G L).card)
    (hj : j < (finiteLeafMeetSupport G L).card)
    (hij : i < j)
    (hiLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) i)
    (hjLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) j) :
    IsOneSplit (finiteSupportGraph G (finiteLeafMeetSupport G L))
      ((finiteSupportGraph G (finiteLeafMeetSupport G L)).oneMeetLevel i j) := by
  have hi3 : 3 ≤ i := hiLeaf.1
  have hj3 : 3 ≤ j := hjLeaf.1
  have hiMem : finiteSupportIndex (finiteLeafMeetSupport G L) i ∈ L :=
    finiteLeafMeetSupport_reindexed_leaf_mem_L D hLeaves i hi3 hi hiLeaf
  have hjMem : finiteSupportIndex (finiteLeafMeetSupport G L) j ∈ L :=
    finiteLeafMeetSupport_reindexed_leaf_mem_L D hLeaves j hj3 hj hjLeaf
  exact finiteLeafMeetSupport_selected_S1
    D hLeaves i j hi hj hij hiMem hjMem

end DiaryLeafPriority
end ThreeUniformDiaries
