import ThreeUniformDiaries.DiaryFiniteHorizonOneMeetStabilisation
import ThreeUniformDiaries.DiaryOneNewLeafSupportSuccessor
import ThreeUniformDiaries.DiaryFiniteGeneratorTable

/-!
# Finite bound for the entire new nonleaf diary generator record

At a genuine new source leaf m, the canonical support adds m and
possibly new singleton and full ordered-pair type meets.
Fix the images f(a) of all previously selected source leaves a<m.

In ANY admissible relative successor g preserving these old leaf
images, every newly supported vertex other than m has target
index at most max { f(a) : a is an old selected source leaf }.

The proof uses only exact leaf S1/S2 meet transport and the capped
numerical type-meet definitions. It does NOT assume an infinite
embedding or a relative new-leaf existence theorem.

Consequently the images of ALL NEW NONLEAF generator vertices have
one of finitely many possible records, independently of the possibly
unbounded image g(m) of the new leaf.

This does not bound g(m) and does not prove countable unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The new genuine nonleaf generator vertices at a leaf step:
the new support minus the old support, excluding the new leaf. -/
noncomputable def newNonleafGeneratorSupport
    (H : Ordered3Graph Nat) (m : Nat) : Finset Nat := by
  classical
  exact (countableDiaryFiniteSupport H (m + 1)).filter
    (fun u => u ∉ countableDiaryFiniteSupport H m ∧ u ≠ m)

theorem mem_newNonleafGeneratorSupport_iff
    (H : Ordered3Graph Nat) (m u : Nat) :
    u ∈ newNonleafGeneratorSupport H m ↔
      u ∈ countableDiaryFiniteSupport H (m + 1) ∧
      u ∉ countableDiaryFiniteSupport H m ∧ u ≠ m := by
  classical
  simp only [newNonleafGeneratorSupport, Finset.mem_filter]

/-- Every new nonleaf generator image is capped by an OLD selected
leaf image. No assumption of a global source or target embedding
is needed, and g(m) may be arbitrarily high. -/
theorem new_nonleaf_generator_image_le_old_leaf_sup
    {H K : Ordered3Graph Nat}
    {F f g : Nat → Nat} {m u : Nat}
    (hm : IsLeaf H m)
    (Q : AdmissibleCofinalDiaryStage H K F (m + 1) g)
    (hKeep : ∀ a : Nat,
      a ∈ countableDiaryLeafPrefix H m → g a = f a)
    (huNew : u ∈ newNonleafGeneratorSupport H m) :
    g u ≤ (countableDiaryLeafPrefix H m).sup f := by
  classical
  let L := countableDiaryLeafPrefix H m
  let L' := countableDiaryLeafPrefix H (m + 1)
  have hL' : L' = insert m L :=
    countableDiaryLeafPrefix_succ_of_leaf H m hm
  obtain ⟨huSupported,huNotOld,huNeM⟩ :=
    (mem_newNonleafGeneratorSupport_iff H m u).mp huNew
  have hOldBound (a : Nat) (ha : a ∈ L) :
      g a ≤ L.sup f := by
    calc
      g a = f a := hKeep a ha
      _ ≤ L.sup f := Finset.le_sup (f := f) ha
  have hLeaf' (a : Nat) (ha : a ∈ L') : IsLeaf H a :=
    ((mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha).2.2
  have hSelectedSupport (a : Nat) (ha : a ∈ L') :
      a ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H L' a ha
  have hSelectedLeM (a : Nat) (ha : a ∈ L') : a ≤ m := by
    have hCut := ((mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha).2.1
    omega
  have hSelectedCases (a : Nat) (ha : a ∈ L') :
      a = m ∨ a ∈ L := by
    rw [hL'] at ha
    exact Finset.mem_insert.mp ha
  have hu : u ∈ finiteLeafMeetSupport H L' := huSupported
  change u ∈
    (Finset.range 3 ∪ L') ∪
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
      obtain ⟨hp,hab⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
      have hOldSome : a ∈ L ∨ b ∈ L := by
        rcases hSelectedCases a ha with haM | haOld
        · rcases hSelectedCases b hb with hbM | hbOld
          · exact False.elim (hab (haM.trans hbM.symm))
          · exact Or.inr hbOld
        · exact Or.inl haOld
      have hMapped : g u = K.oneMeetLevel (g a) (g b) := by
        simpa only [hEq] using
          (Q.leaf_oneMeet a b
            (hSelectedSupport a ha) (hSelectedSupport b hb)
            (hLeaf' a ha) (hLeaf' b hb)).symm
      have hCap := K.oneMeetLevel_le_min (g a) (g b)
      rcases hOldSome with haOld | hbOld
      · exact (hMapped.le.trans
          (hCap.trans (min_le_left _ _))).trans (hOldBound a haOld)
      · exact (hMapped.le.trans
          (hCap.trans (min_le_right _ _))).trans (hOldBound b hbOld)
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
      have hMapped : g u =
          K.twoMeetLevel (g a) (g b) (g c) (g d) := by
        simpa only [hEq] using
          (Q.leaf_twoMeet a b c d
            (hSelectedSupport a ha) (hSelectedSupport b hb)
            (hSelectedSupport c hc) (hSelectedSupport d hd)
            hab hcd
            (hLeaf' a ha) (hLeaf' b hb)
            (hLeaf' c hc) (hLeaf' d hd)).symm
      have hCap := K.twoMeetLevel_le_min (g a) (g b) (g c) (g d)
      have hUleA : g u ≤ g a := by
        calc
          g u = K.twoMeetLevel (g a) (g b) (g c) (g d) := hMapped
          _ ≤ min (g a) (g c) := hCap
          _ ≤ g a := min_le_left _ _
      exact hUleA.trans (hOldBound a haOld)

/-- There is one EXPLICIT finite set of complete new nonleaf
generator records covering the image profile of every relative
successor keeping the old selected leaf values fixed. -/
theorem exists_finite_new_nonleaf_profile_cover
    {H K : Ordered3Graph Nat}
    {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m) :
    ∃ W : Finset
        ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat),
      ∀ (g : Nat → Nat),
        AdmissibleCofinalDiaryStage H K F (m + 1) g →
        (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m → g a = f a) →
        (fun u : {u : Nat // u ∈ newNonleafGeneratorSupport H m} =>
          g u.val) ∈ W := by
  classical
  let L := countableDiaryLeafPrefix H m
  let M := L.sup f
  let T := {u : Nat // u ∈ newNonleafGeneratorSupport H m}
  let W : Finset (T → Nat) :=
    Finset.univ.image
      (fun p : T → Fin (M + 1) => fun u : T => (p u).val)
  refine ⟨W,?_⟩
  intro g Q hKeep
  let p : T → Fin (M + 1) := fun u =>
    ⟨g u.val, by
      have hBound := new_nonleaf_generator_image_le_old_leaf_sup
        hm Q hKeep u.property
      change g u.val ≤ M at hBound
      omega⟩
  change (fun u : T => g u.val) ∈ W
  apply Finset.mem_image.mpr
  refine ⟨p,Finset.mem_univ _,?_⟩
  rfl

end DiaryLeafPriority
end ThreeUniformDiaries
