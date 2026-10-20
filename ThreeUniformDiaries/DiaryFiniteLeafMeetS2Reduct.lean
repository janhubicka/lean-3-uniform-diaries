import ThreeUniformDiaries.DiaryFiniteLeafMeetS1Reduct
import ThreeUniformDiaries.DiaryFiniteLeafMeetTwoSplitDisagreement
import ThreeUniformDiaries.DiaryFiniteLeafMeetCapTransfer
import ThreeUniformDiaries.DiaryFiniteLeafMeetMarkerOneDisagreement

/-!
# The complete S2 axiom for the finite leaf-meet reduct

In a countable RoleDiary every comparison of two increasing leaf
pairs has full two-meet of precisely one of three forms:
* marker 1;
* a genuine two-split;
* the cap at the smaller first coordinate.

All genuine leaves of the generated support S_L belong to L.
The three cases survive strictly increasing finite compression:
* marker 1: the retained Devlin-1 auxiliary bit distinguishes
  the two pairs (verified marker-one compression lemma);
* genuine two-split: that split lies in S_L, and the retained
  auxiliary incidence at the split distinguishes the pairs;
* cap: forward type agreement and the cap alone give equality.

Therefore EVERY pair of genuine leaves of the finite induced
support satisfies the literal finite S2 axiom. The proof uses no
false converse to generic type compression.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {L : Finset Nat}

/-- Binary minimum commutes with any increasing finite support
enumeration at selected legitimate indices. -/
theorem finiteSupportIndex_min_below
    (S : Finset Nat) (i j : Nat)
    (hi : i < S.card) (hj : j < S.card) :
    finiteSupportIndex S (min i j) =
      min (finiteSupportIndex S i) (finiteSupportIndex S j) := by
  rcases le_total i j with hij | hji
  · rw [min_eq_left hij, min_eq_left
      (finiteSupportIndex_mono_below S i j hi hj hij)]
  · rw [min_eq_right hji, min_eq_right
      (finiteSupportIndex_mono_below S j i hj hi hji)]

/-- ALL ordered leaf-pair comparisons in the extracted finite
support satisfy S2. The three original source alternatives
are handled by three exact finite first-disagreement theorems,
not by a nonexistent backwards generic type-transfer rule. -/
theorem finiteLeafMeetSupport_reindexed_S2
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (i j p q : Nat)
    (hi : i < (finiteLeafMeetSupport G L).card)
    (hj : j < (finiteLeafMeetSupport G L).card)
    (hp : p < (finiteLeafMeetSupport G L).card)
    (hq : q < (finiteLeafMeetSupport G L).card)
    (hij : i < j) (hpq : p < q)
    (hiLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) i)
    (hjLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) j)
    (hpLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) p)
    (hqLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) q) :
    (finiteSupportGraph G (finiteLeafMeetSupport G L)).twoMeetLevel i j p q =
      min i p ∨
    (finiteSupportGraph G (finiteLeafMeetSupport G L)).twoMeetLevel i j p q = 1 ∨
    IsTwoSplit (finiteSupportGraph G (finiteLeafMeetSupport G L))
      ((finiteSupportGraph G (finiteLeafMeetSupport G L)).twoMeetLevel i j p q) := by
  classical
  let S := finiteLeafMeetSupport G L
  let H := finiteSupportGraph G S
  let A := finiteSupportIndex S i
  let B := finiteSupportIndex S j
  let C := finiteSupportIndex S p
  let E := finiteSupportIndex S q
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker G L 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker G L 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker G L 2 (by omega)
  have hAi : A ∈ L :=
    finiteLeafMeetSupport_reindexed_leaf_mem_L D hLeaves
      i hiLeaf.1 hi hiLeaf
  have hBj : B ∈ L :=
    finiteLeafMeetSupport_reindexed_leaf_mem_L D hLeaves
      j hjLeaf.1 hj hjLeaf
  have hCp : C ∈ L :=
    finiteLeafMeetSupport_reindexed_leaf_mem_L D hLeaves
      p hpLeaf.1 hp hpLeaf
  have hEq : E ∈ L :=
    finiteLeafMeetSupport_reindexed_leaf_mem_L D hLeaves
      q hqLeaf.1 hq hqLeaf
  have hALeaf : IsLeaf G A := hLeaves A hAi
  have hBLeaf : IsLeaf G B := hLeaves B hBj
  have hCLeaf : IsLeaf G C := hLeaves C hCp
  have hELeaf : IsLeaf G E := hLeaves E hEq
  have hAB : A < B := finiteSupportIndex_strictMono S i j hij hj
  have hCE : C < E := finiteSupportIndex_strictMono S p q hpq hq
  let m := G.twoMeetLevel A B C E
  rcases D.pair_meets A B C E hAB hCE
      hALeaf hBLeaf hCLeaf hELeaf with hCap | hMarker | hSplit
  · have hCapIndex :
        G.twoMeetLevel A B C E = finiteSupportIndex S (min i p) := by
      rw [hCap]
      exact (finiteSupportIndex_min_below S i p hi hp).symm
    left
    exact finiteSupportGraph_capped_twoMeet_exact
      (G := G) (S := S) i j p q hi hj hp hq hij hpq hCapIndex
  · right
    left
    exact finiteSupportGraph_twoMeet_exact_at_marker_one
      D h0 h1 h2 i j p q hi hj hp hq hij hpq
      hiLeaf.1 hpLeaf.1 hALeaf hBLeaf hCLeaf hELeaf hMarker
  · have hmMem : m ∈ S :=
      mem_finiteLeafMeetSupport_twoMeet G L
        A B C E hAB hCE hAi hBj hCp hEq
    obtain ⟨k,hk,hkm⟩ := finiteSupportIndex_surjective_on S m hmMem
    have hSplitM : IsTwoSplit G m := hSplit
    have hk3 : 3 ≤ k :=
      finiteSupportIndex_ge_three_of_image S k h0 h1 h2 hk
        (by simpa only [hkm] using hSplitM.1)
    have hmBound : m ≤ min A C := G.twoMeetLevel_le_min A B C E
    have hma : m < A := by
      have hle := hmBound.trans (min_le_left _ _)
      have hne : m ≠ A := by
        intro h
        have hSplitA : IsTwoSplit G A := by
          simpa only [h] using hSplitM
        exact hALeaf.2.2 hSplitA.2.2
      omega
    have hmc : m < C := by
      have hle := hmBound.trans (min_le_right _ _)
      have hne : m ≠ C := by
        intro h
        have hSplitC : IsTwoSplit G C := by
          simpa only [h] using hSplitM
        exact hCLeaf.2.2 hSplitC.2.2
      omega
    have hki : k < i :=
      finiteSupportIndex_lt_of_image_lt S k i hk hi
        (by simpa only [hkm] using hma)
    have hkp : k < p :=
      finiteSupportIndex_lt_of_image_lt S k p hk hp
        (by simpa only [hkm] using hmc)
    have hIndexedSplit : IsTwoSplit H k :=
      (finiteSupportGraph_twoSplit_iff
        (G := G) (S := S) h0 h1 h2 k hk3 hk).mpr
          (by simpa only [hkm] using hSplitM)
    have hExact : H.twoMeetLevel i j p q = k :=
      finiteSupportGraph_twoMeet_exact_at_retained_twoSplit
        D i j p q k hi hj hp hq hk hij hpq hki hkp
        (by simpa only [hkm] using hSplitM)
        (by simpa only [hkm] using (show
          G.twoMeetLevel A B C E = m from rfl))
    right
    rw [hExact]
    exact Or.inr hIndexedSplit

end DiaryLeafPriority
end ThreeUniformDiaries
