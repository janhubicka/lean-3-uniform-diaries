import ThreeUniformDiaries.DiaryFutureReserveFusion
import ThreeUniformDiaries.DiaryOneNewLeafSupportSuccessor
import ThreeUniformDiaries.DiaryCountableRelativeMarkerBase

/-!
# The first selected source leaf always has a reserved successor

The first genuinely new source leaf m introduces NO other leaf-meet
generators: there are no two distinct selected leaves and no ordered
pair of selected leaves yet. Its successor support is exactly the
three fixed markers together with m.

Consequently any sufficiently high actual target leaf from the
prescribed outer range supplies a complete reserved successor,
independent of the finite flip absorber or genericity of target leaf
triples. This is a genuine positive local existence result, but
NOT a new-leaf theorem when the old support already has leaves.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The closure of a singleton selected leaf has no genuine
singleton/pair-meet generators in addition to that leaf. -/
theorem finiteLeafMeetSupport_singleton
    (H : Ordered3Graph Nat) (m : Nat) :
    finiteLeafMeetSupport H ({m} : Finset Nat) =
      Finset.range 3 ∪ {m} := by
  classical
  simp [finiteLeafMeetSupport, finiteOneMeetSupport,
    finiteTwoMeetSupport, finiteOrderedLeafPairs]

/-- If no earlier source leaves have been selected, adding the
first leaf gives exactly four supported vertices: markers and
the new leaf itself. -/
theorem countableDiaryFiniteSupport_first_leaf
    (H : Ordered3Graph Nat) (m : Nat)
    (hm : IsLeaf H m)
    (hEmpty : countableDiaryLeafPrefix H m = ∅) :
    countableDiaryFiniteSupport H (m + 1) =
      Finset.range 3 ∪ {m} := by
  rw [countableDiaryFiniteSupport_succ_of_leaf H m hm,
    hEmpty, Finset.insert_empty]
  exact finiteLeafMeetSupport_singleton H m

/-- A full diary has no edge whose increasing vertices are
chosen from the three markers and a single genuine leaf.
In particular the first-leaf four-vertex support has the
same induced edge/nonedge pattern in EVERY full diary. -/
theorem RoleDiary.no_edge_in_marker_leaf_support
    {H : Ordered3Graph Nat} (D : RoleDiary H)
    {m a b c : Nat} (hm : IsLeaf H m)
    (ha : a < 3 ∨ a = m)
    (hb : b < 3 ∨ b = m)
    (hc : c < 3 ∨ c = m)
    (hab : a < b) (hbc : b < c) :
    ¬ H.edge a b c := by
  have haSmall : a < 3 := by
    rcases ha with hsmall | hEq
    · exact hsmall
    · rcases hb with hsmall | hEqB <;> omega
  have hbSmall : b < 3 := by
    rcases hb with hsmall | hEq
    · exact hsmall
    · rcases hc with hsmall | hEqC <;> omega
  intro he
  rcases D.permitted_edge a b c he with
    hE1 | hE2 | hE3 | hE4 | hE5
  · obtain ⟨haZero,hB,hC⟩ := hE1
    have hcEq : c = m := by rcases hc with hSmall | hEq <;> omega
    rcases hB with hbOne | hbTwo
    · have hEqA : a = 0 := haZero
      have hEqB : b = 1 := hbOne
      subst a
      subst b
      subst c
      exact hm.2.1 he
    · have hEqA : a = 0 := haZero
      have hEqB : b = 2 := hbTwo
      subst a
      subst b
      subst c
      exact hm.2.2 he
  · have hOne : IsOneSplit H b := hE2.2.1
    omega
  · have hTwo : IsTwoSplit H a := hE3.1
    omega
  · have hLeafB : IsLeaf H b := hE4.2.1
    omega
  · have hLeafA : IsLeaf H a := hE5.1
    omega

/-- A FIRST source leaf m can always be placed at any prescribed
target leaf v at level >=m, with an exact full induced support
map and enough numerical room for every future source level.

The prescribed leaf range is arbitrary except that it contains
the indicated actual target leaf. No generic hypergraph property
is used: with just one selected source leaf, there are no
nontrivial S1/S2 meets and no nonmarker induced triples. -/
theorem exists_reserved_successor_of_first_leaf
    {H K : Ordered3Graph Nat}
    {F f : Nat → Nat} {m t : Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (hm : IsLeaf H m)
    (hEmpty : countableDiaryLeafPrefix H m = ∅)
    (hFleaf : IsLeaf K (F t))
    (hHigh : m ≤ F t) :
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) := by
  classical
  let v := F t
  let g : Nat → Nat := fun u => if u = m then v else u
  have hSupport :
      countableDiaryFiniteSupport H (m + 1) =
        Finset.range 3 ∪ {m} :=
    countableDiaryFiniteSupport_first_leaf H m hm hEmpty
  have hCase (u : Nat)
      (hu : u ∈ countableDiaryFiniteSupport H (m + 1)) :
      u < 3 ∨ u = m := by
    rw [hSupport] at hu
    rcases Finset.mem_union.mp hu with hMarker | hNew
    · exact Or.inl (Finset.mem_range.mp hMarker)
    · exact Or.inr (Finset.mem_singleton.mp hNew)
  have hMarkerImage (u : Nat) (hu : u < 3) : g u = u := by
    have hne : u ≠ m := by
      have hm3 := hm.1
      omega
    simp [g,hne]
  have hLeafImage : g m = v := by simp [g]
  have hTargetCase (u : Nat)
      (hu : u ∈ countableDiaryFiniteSupport H (m + 1)) :
      g u < 3 ∨ g u = v := by
    rcases hCase u hu with hSmall | hEq
    · left
      rw [hMarkerImage u hSmall]
      exact hSmall
    · right
      subst u
      exact hLeafImage
  have hOrder (a b : Nat)
      (ha : a ∈ countableDiaryFiniteSupport H (m + 1))
      (hb : b ∈ countableDiaryFiniteSupport H (m + 1))
      (hab : a < b) : g a < g b := by
    have haSmall : a < 3 := by
      rcases hCase a ha with hSmall | hEq
      · exact hSmall
      · rcases hCase b hb with hSmall | hEqB <;> omega
    have hGa : g a = a := hMarkerImage a haSmall
    rcases hCase b hb with hbSmall | hbEq
    · have hGb : g b = b := hMarkerImage b hbSmall
      omega
    · subst b
      rw [hGa,hLeafImage]
      have hm3 := hm.1
      omega
  have hStage : AdmissibleCofinalDiaryStage H K F (m + 1) g := by
    refine {
      ordered := hOrder
      marker_zero := hMarkerImage 0 (by omega)
      marker_one := hMarkerImage 1 (by omega)
      marker_two := hMarkerImage 2 (by omega)
      leaf_role := ?_
      one_split_role := ?_
      two_split_role := ?_
      induced_edge := ?_
      leaf_oneMeet := ?_
      leaf_twoMeet := ?_
      leaf_range := ?_
    }
    · intro u hu hLeaf
      rcases hCase u hu with hSmall | hEq
      · have h3 := hLeaf.1
        omega
      · subst u
        rw [hLeafImage]
        exact hFleaf
    · intro u hu hOne
      rcases hCase u hu with hSmall | hEq
      · have h3 := hOne.1
        omega
      · subst u
        exact False.elim (hm.2.1 hOne.2.1)
    · intro u hu hTwo
      rcases hCase u hu with hSmall | hEq
      · have h3 := hTwo.1
        omega
      · subst u
        exact False.elim (hm.2.2 hTwo.2.2)
    · intro a b c ha hb hc hab hbc
      have hGa := hTargetCase a ha
      have hGb := hTargetCase b hb
      have hGc := hTargetCase c hc
      have hab' := hOrder a b ha hb hab
      have hbc' := hOrder b c hb hc hbc
      have hNoH := DH.no_edge_in_marker_leaf_support hm
        (hCase a ha) (hCase b hb) (hCase c hc) hab hbc
      have hNoK := DK.no_edge_in_marker_leaf_support hFleaf
        hGa hGb hGc hab' hbc'
      tauto
    · intro a b ha hb hLa hLb
      have haM : a = m := by
        rcases hCase a ha with hSmall | hEq
        · have h3 := hLa.1
          omega
        · exact hEq
      have hbM : b = m := by
        rcases hCase b hb with hSmall | hEq
        · have h3 := hLb.1
          omega
        · exact hEq
      subst a
      subst b
      simp only [Ordered3Graph.oneMeetLevel_self]
    · intro a b c d ha hb hc hd hab hcd hLa hLb hLc hLd
      have haM : a = m := by
        rcases hCase a ha with hSmall | hEq
        · have h3 := hLa.1
          omega
        · exact hEq
      have hbM : b = m := by
        rcases hCase b hb with hSmall | hEq
        · have h3 := hLb.1
          omega
        · exact hEq
      omega
    · intro u hu hLeaf
      rcases hCase u hu with hSmall | hEq
      · have h3 := hLeaf.1
        omega
      · subst u
        exact ⟨t,hLeafImage⟩
  have hReserve : FutureOrderReserve H (m + 1) g := by
    intro x y hx hy hxy
    have hxSmall : x < 3 := by
      rcases hCase x hx with hSmall | hEq
      · exact hSmall
      · rcases hCase y hy with hSmall | hEqY <;> omega
    rcases hCase y hy with hySmall | hyEq
    · rw [hMarkerImage x hxSmall, hMarkerImage y hySmall]
      omega
    · subst y
      rw [hMarkerImage x hxSmall,hLeafImage]
      omega
  refine ⟨g,⟨hStage,hReserve⟩,?_⟩
  intro u hu
  rw [hEmpty] at hu
  exact False.elim (Finset.not_mem_empty u hu)

end DiaryLeafPriority
end ThreeUniformDiaries
