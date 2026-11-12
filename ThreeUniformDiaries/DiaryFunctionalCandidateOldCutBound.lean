import ThreeUniformDiaries.DiaryFunctionalCandidateOldSupport
import ThreeUniformDiaries.DiaryUniformOldStageTailColour

/-!
# Track A: functional candidate tables have a fixed old-stage numerical cut

A PROPOSED next-leaf candidate need not yet satisfy target roles, the
induced E2/E3/E5 edge/nonedge table, numeric source order or future
reserve. Nevertheless, if its complete S1/S2 leaf-generator table
is FUNCTIONAL, every newly generated NONLEAF source coordinate has
a target image bounded by the maximum of the OLD selected target
leaf values f(a), independently of the potentially arbitrary new
leaf image v.

The proof is a literal decomposition of the finite generated support:
markers and selected old/new leaves are not genuinely new nonleaf
generators; a fresh singleton meet has at least one old selected
leaf argument, and any fresh full two-type meet of ordered selected
pairs has an OLD first leaf argument because the newly selected
source leaf m is largest. The capped numeric target meets bound
the forced table images accordingly. Only functionality and the
fact m is a genuine new SOURCE leaf are needed.

With an actual old admissible stage P, the earlier old-support
rigidity theorem covers old vertices. Combining the two facts gives
ONE numerical cut determined only by P, below which EVERY candidate
image except the new source leaf m lies, BEFORE any candidate is
known to satisfy role/order/edge/reserve tests.

This does not construct a functional candidate, prove its correctness,
or establish relative no-escape or diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A functional proposed generator table forces each genuinely new
nonleaf image below the old selected-leaf numerical supremum.
No actual old or new admissible stage, no target full RoleDiary,
no ordering, role or edge hypothesis is required. -/
theorem functional_candidate_new_nonleaf_image_le_old_leaf_sup
    {H K : Ordered3Graph Nat} {f : Nat → Nat} {m v u : Nat}
    (hm : IsLeaf H m)
    (hFunctional : FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f v))
    (huNew : u ∈ newNonleafGeneratorSupport H m) :
    candidateNewLeafTableMap H K m f v u ≤
      (countableDiaryLeafPrefix H m).sup f := by
  classical
  let L := countableDiaryLeafPrefix H m
  let L' := countableDiaryLeafPrefix H (m + 1)
  let q := candidateLeafImage f m v
  let g := candidateNewLeafTableMap H K m f v
  let T := candidateNewLeafGeneratorTable H K m f v
  have hL' : L' = insert m L :=
    countableDiaryLeafPrefix_succ_of_leaf H m hm
  have hSelectedLeM (a : Nat) (ha : a ∈ L') : a ≤ m := by
    have hCut :=
      ((mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha).2.1
    omega
  have hSelectedCases (a : Nat) (ha : a ∈ L') :
      a = m ∨ a ∈ L := by
    rw [hL'] at ha
    exact Finset.mem_insert.mp ha
  have hOldBound (a : Nat) (ha : a ∈ L) : q a ≤ L.sup f := by
    have haLt : a < m :=
      ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.1
    have hq : q a = f a := by
      simp [q, candidateLeafImage, ne_of_lt haLt]
    rw [hq]
    exact Finset.le_sup (f := f) ha
  have hValue (x y : Nat) (hRow : (x,y) ∈ T) : g x = y := by
    exact finiteGeneratorTableValue_eq_of_mem
      T hFunctional x y hRow
  obtain ⟨huSupported, huNotOld, huNeM⟩ :=
    (mem_newNonleafGeneratorSupport_iff H m u).mp huNew
  have hu : u ∈ finiteLeafMeetSupport H L' := huSupported
  change u ∈ (Finset.range 3 ∪ L') ∪
    (finiteOneMeetSupport H L' ∪ finiteTwoMeetSupport H L') at hu
  rcases Finset.mem_union.mp hu with hFront | hMeets
  · rcases Finset.mem_union.mp hFront with hMarker | hLeaf
    · exact False.elim (huNotOld
        (mem_finiteLeafMeetSupport_marker H L u
          (Finset.mem_range.mp hMarker)))
    · rcases hSelectedCases u hLeaf with huM | huL
      · exact False.elim (huNeM huM)
      · exact False.elim
          (huNotOld (mem_finiteLeafMeetSupport_leaf H L u huL))
  · rcases Finset.mem_union.mp hMeets with hOne | hTwo
    · change u ∈ ((L'.product L').filter
          (fun p : Nat × Nat => p.1 ≠ p.2)).image
          (fun p : Nat × Nat => H.oneMeetLevel p.1 p.2) at hOne
      obtain ⟨⟨a,b⟩,hp,hEq⟩ := Finset.mem_image.mp hOne
      change H.oneMeetLevel a b = u at hEq
      obtain ⟨hp, hab⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
      have hOldSome : a ∈ L ∨ b ∈ L := by
        rcases hSelectedCases a ha with haM | haOld
        · rcases hSelectedCases b hb with hbM | hbOld
          · exact False.elim (hab (haM.trans hbM.symm))
          · exact Or.inr hbOld
        · exact Or.inl haOld
      have hRow :
          (H.oneMeetLevel a b, K.oneMeetLevel (q a) (q b)) ∈ T :=
        finiteLeafGeneratorTable_oneMeet H K L' q a b ha hb hab
      have hMapped : g u = K.oneMeetLevel (q a) (q b) := by
        simpa only [hEq] using
          hValue (H.oneMeetLevel a b) (K.oneMeetLevel (q a) (q b))
            hRow
      rcases hOldSome with haOld | hbOld
      · calc
          g u = K.oneMeetLevel (q a) (q b) := hMapped
          _ ≤ min (q a) (q b) := K.oneMeetLevel_le_min (q a) (q b)
          _ ≤ q a := min_le_left _ _
          _ ≤ L.sup f := hOldBound a haOld
      · calc
          g u = K.oneMeetLevel (q a) (q b) := hMapped
          _ ≤ min (q a) (q b) := K.oneMeetLevel_le_min (q a) (q b)
          _ ≤ q b := min_le_right _ _
          _ ≤ L.sup f := hOldBound b hbOld
    · change u ∈
        ((finiteOrderedLeafPairs L').product
          (finiteOrderedLeafPairs L')).image
          (fun p : (Nat × Nat) × (Nat × Nat) =>
            H.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2) at hTwo
      obtain ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,hp,hEq⟩ :=
        Finset.mem_image.mp hTwo
      change H.twoMeetLevel a b c d = u at hEq
      obtain ⟨hpAB,hpCD⟩ := Finset.mem_product.mp hp
      obtain ⟨hpAB,hab⟩ := Finset.mem_filter.mp hpAB
      obtain ⟨hpCD,hcd⟩ := Finset.mem_filter.mp hpCD
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hpAB
      obtain ⟨hc,hd⟩ := Finset.mem_product.mp hpCD
      have haOld : a ∈ L := by
        rcases hSelectedCases a ha with haM | hOld
        · have hbBound := hSelectedLeM b hb
          have hmb : m < b := by simpa only [haM] using hab
          exact False.elim ((not_lt_of_ge hbBound) hmb)
        · exact hOld
      have hRow :
          (H.twoMeetLevel a b c d,
            K.twoMeetLevel (q a) (q b) (q c) (q d)) ∈ T :=
        finiteLeafGeneratorTable_twoMeet H K L'
          q a b c d ha hb hc hd hab hcd
      have hMapped : g u =
          K.twoMeetLevel (q a) (q b) (q c) (q d) := by
        simpa only [hEq] using
          hValue (H.twoMeetLevel a b c d)
            (K.twoMeetLevel (q a) (q b) (q c) (q d)) hRow
      calc
        g u = K.twoMeetLevel (q a) (q b) (q c) (q d) := hMapped
        _ ≤ min (q a) (q c) :=
          K.twoMeetLevel_le_min (q a) (q b) (q c) (q d)
        _ ≤ q a := min_le_left _ _
        _ ≤ L.sup f := hOldBound a haOld

/-- All proposed supported images other than the new source leaf
lie below ONE numerical cut depending ONLY on the actual old stage,
already under the purely algebraic table-functionality assumption.

In particular this cut can be fixed before finding any new target
leaf v and without presupposing a genuine relative successor. -/
theorem AdmissibleCofinalDiaryStage.functional_candidate_other_below_oldStageTailCut
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v u : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hFunctional : FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f v))
    (hu : u ∈ countableDiaryFiniteSupport H (m + 1))
    (hum : u ≠ m) :
    candidateNewLeafTableMap H K m f v u <
      oldStageTailCut H m f := by
  classical
  let g := candidateNewLeafTableMap H K m f v
  by_cases huOld : u ∈ countableDiaryFiniteSupport H m
  · have huFix : g u = f u :=
      P.functional_candidate_table_preserves_old_support hFunctional u huOld
    change g u <
      max ((countableDiaryFiniteSupport H m).sup f)
          ((countableDiaryLeafPrefix H m).sup f) + 1
    calc
      g u = f u := huFix
      _ ≤ (countableDiaryFiniteSupport H m).sup f :=
        Finset.le_sup (f := f) huOld
      _ ≤ max ((countableDiaryFiniteSupport H m).sup f)
          ((countableDiaryLeafPrefix H m).sup f) :=
        le_max_left _ _
      _ < max ((countableDiaryFiniteSupport H m).sup f)
          ((countableDiaryLeafPrefix H m).sup f) + 1 :=
        Nat.lt_succ_self _
  · have huNew : u ∈ newNonleafGeneratorSupport H m :=
      (mem_newNonleafGeneratorSupport_iff H m u).mpr
        ⟨hu, huOld, hum⟩
    have hBound : g u ≤ (countableDiaryLeafPrefix H m).sup f :=
      functional_candidate_new_nonleaf_image_le_old_leaf_sup
        hm hFunctional huNew
    change g u <
      max ((countableDiaryFiniteSupport H m).sup f)
          ((countableDiaryLeafPrefix H m).sup f) + 1
    exact lt_of_le_of_lt
      (hBound.trans (le_max_right _ _))
      (Nat.lt_succ_self _)

end DiaryLeafPriority
end ThreeUniformDiaries
