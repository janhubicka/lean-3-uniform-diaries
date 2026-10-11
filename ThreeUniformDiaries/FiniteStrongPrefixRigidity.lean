import ThreeUniformDiaries.InfiniteToFiniteStrongPrefix
import ThreeUniformDiaries.InfiniteStrongSelectedAncestors
import ThreeUniformDiaries.MeetClosedGapRigidity

/-!
# Rigidity: a finite strong S inside U equals the initial strong prefix of U

Suppose S is a genuine finite strong picture of selected height k+1
and U a genuine infinite strong picture, on the same selected level
map f, with the SAME root. If S⊆U, then S is exactly the first k+1
selected levels of U.

Proof: by induction on selected levels. If p is already in S and x
is a selected U-child of p, then S has its representative z in the
corresponding ambient immediate-child cone. Both x and z are in U
at the same next selected level; ambient meet closure and the empty
selected-level gap force x=z. This proves no extra U nodes occur in
the initial finite levels.

The result bridges infinite extension of a finite strong picture to
finite/infinite canonical-map coherence without any hidden
surjectivity or precompactness assumptions.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finiteStrongPicture_eq_infinitePrefix_of_subset
    {S U : Set CoordNode} {f : Nat → Nat} {r : CoordNode}
    {k : Nat}
    (hS : FiniteStrongPicture S f k r)
    (hU : InfiniteStrongPicture U f r)
    (hf : StrictMono f) (hr : level r = f 0)
    (hSU : S ⊆ U) :
    S = infiniteStrongPicture_finitePrefix U f k := by
  obtain ⟨hfinite, hclosed, hroot, hbelow,
      hlevelsS, hallS, hnextS⟩ := hS
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi, hl⟩ := hlevelsS x hx
    exact ⟨hSU hx, by rw [hl]; exact hf.monotone hi⟩
  · intro x hx
    obtain ⟨i, hi⟩ := hU.selected_levels x hx.1
    have hik : i ≤ k := by
      have hle := hx.2
      rw [hi] at hle
      by_contra hnot
      have hki : k < i := Nat.lt_of_not_ge hnot
      exact (not_le_of_gt (hf hki)) hle
    have hselected :
        ∀ (j : Nat), j ≤ k →
          ∀ (y : CoordNode), y ∈ U →
            level y = f j → y ∈ S := by
      intro j
      induction j with
      | zero =>
          intro hj y hy hyLevel
          have hry : r ≤ y := hU.root_le y hy
          have heq : r = y :=
            eq_of_le_of_level_eq hry (hr.trans hyLevel.symm)
          rw [← heq]
          exact hroot
      | succ j ih =>
          intro hj y hy hyLevel
          have hprev : f j ≤ f (j + 1) :=
            hf.monotone (Nat.le_succ j)
          have hjk : j ≤ k := by omega
          let p := truncate y (f j)
          have hpU : p ∈ U :=
            infiniteStrongPicture_selected_truncate_mem
              hU hf hr j (j + 1) (Nat.le_succ j) y hy hyLevel
          have hpLevel : level p = f j := by simp [p]
          have hpS : p ∈ S := ih hjk p hpU hpLevel
          let t := truncate y (f j + 1)
          have htLevel : level t = f j + 1 := by simp [t]
          have hty : t ≤ y :=
            truncate_le y (by rw [hyLevel]; omega)
          have hpt : p ≤ t := by
            refine ⟨by rw [hpLevel, htLevel]; omega, ?_⟩
            change truncate t (level p) = p
            calc
              truncate t (level p) = truncate y (level p) := by
                dsimp [t]
                exact truncate_truncate y (by rw [hpLevel]; omega)
              _ = p := by rw [hpLevel]
          have hcover : p ⋖ t := by
            apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpt
            change level t = level p + 1
            rw [htLevel, hpLevel]
          obtain ⟨z, ⟨hzS, hzLevel, htz⟩, _⟩ :=
            hnextS j hj p hpS hpLevel t hcover
          have hzU : z ∈ U := hSU hzS
          have hgap :
              AvoidsOpenLevelGap U (f j) (f (j + 1)) :=
            avoids_gaps_of_selected_levels U f hf
              hU.selected_levels j
          have hfj : f j < f (j + 1) :=
            hf (Nat.lt_succ_self j)
          have hlt : f j < level t := by
            rw [htLevel]
            omega
          have hzEq : z = y :=
            unique_above_selected_gap U hU.meet_closed
              (f j) (f (j + 1)) hfj hgap
              z y t hzU hy hzLevel hyLevel htz hty hlt
          rw [← hzEq]
          exact hzS
    exact hselected i hik x hx.1 hi

end CoordNode
end ThreeUniformDiaries
